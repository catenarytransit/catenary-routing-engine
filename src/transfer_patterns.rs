use crate::NodeType;
//THE FINAL BOSS
//use crate::coord_int_convert::*;
//use crate::RoadNetwork;
use crate::{transit_dijkstras::*, transit_network::*};
//use crate::road_dijkstras::*;
use geo::{point, Distance, Haversine, Point};
//use rstar::*;
use serde::{Deserialize, Serialize};
use std::collections::hash_map::Entry;
use std::collections::{BinaryHeap, HashMap, HashSet};
use std::sync::Arc;
use std::sync::Mutex;
use std::thread;
use std::time::Instant;
use petgraph::{graph::*, algo::dijkstra::dijkstra};

//only calculate global time expanded dijkstra from hubs (important stations) to save complexity
//picks important hubs if they are more often visted from Dijkstras-until-all-nodes-settled
pub fn hub_selection(
    router: &TransitDijkstra,
    random_samples: u32,
    _cost_limit: u64,
    num_stations: usize
) -> HashSet<i64> {
    //station ids
    let mut selected_hubs: HashSet<i64> = HashSet::new();

    let mut graph = Graph::new();

    for (tail, head, cost) in router.graph.raw_edges().iter().map(|e|(e.source(), e.target(), e.weight)){
        let ti_tail = router.graph.node_weight(tail).unwrap().station_id;
        let u = graph.add_node(ti_tail);

        let ti_head = router.graph.node_weight(head).unwrap().station_id;
        let v = graph.add_node(ti_head);

        graph.add_edge(u, v, cost);
    }

    //let mut time_independent_router = TransitDijkstra::new(&graph);
    //time_independent_router.set_cost_upper_bound(cost_limit);

    let mut hub_list: HashMap<NodeIndex, u16> = HashMap::new();

    for _ in 0..random_samples {
        let current_node = router.get_random_node_id().unwrap();
        let visited_nodes = dijkstra(&graph,current_node, None, |_| 1);
        for (node, _) in visited_nodes.iter() {
            match hub_list.entry(*node) {
                Entry::Occupied(mut o) => {
                    let counter = o.get_mut();
                    *counter += 1;
                }
                Entry::Vacant(v) => {
                    v.insert(1);
                }
            }
        }
    }

    let mut sorted_hubs: BinaryHeap<(u16, NodeIndex)> =
        hub_list.into_iter().map(|(n, c)| (c, n)).collect();

    for _ in 0..(1.max(num_stations  as u32 /100)) {
        let hub = sorted_hubs.pop().unwrap();
        let station = graph.node_weight(hub.1).unwrap();
        selected_hubs.insert(*station);
    }

    //time_independent_router.set_cost_upper_bound(u64::MAX); //reset cost upper bound to max

    selected_hubs
}

// Precompute transfer patterns from a given station to all other stations.
// Return the transfer patterns & numbers between each station pair.
pub fn num_transfer_patterns_from_source(
    source_station_id: i64,
    router: &TransitDijkstra,
    hubs: Option<&HashSet<i64>>,
    start_time: Option<u64>,
    thread_num: usize
) -> (Mutex<Vec<Vec<NodeId>>>, Instant) {
    println!("start tp calc \t");
    let now = Instant::now();
    let source_transfer_nodes: Vec<NodeId> = router
        .graph
        .node_weights()
        .filter(|node| {
            node.station_id == source_station_id
                && (node.node_type == NodeType::Transfer
                    || (hubs.is_none() && node.node_type == NodeType::Arrival))
                && node.time >= start_time
        })
        //must check for transfer nodes, but checking for arrival nodes may improve query time at expense of longer precompute
        .copied()
        .collect();
    println!("found sources {:?}", now.elapsed());
    let now = Instant::now();

    let visited_nodes = router.time_expanded_dijkstra(source_transfer_nodes, hubs);

    println!("visited nodes {:?}", now.elapsed());
    let now = Instant::now();

    let mut arrival_nodes: Vec<(NodeId, Vec<NodeId>, u64)> = visited_nodes
        .into_iter()
        .map(|(idx, path)| (*router.graph.node_weight(idx).unwrap(), path))
        .filter(|(node, _)| node.node_type == NodeType::Arrival)
        .map(|(node, pathed_node)| {
            let (path, cost) = pathed_node.get_path();
            (node, path, cost)
        })
        .collect();
    println!("filtered arrivals {:?}", now.elapsed());
    let now = Instant::now();

    arrival_loop(&mut arrival_nodes);
    println!("arrival loop {:?}", now.elapsed());
    let now = Instant::now();

    let total_transfer_patterns = Arc::new(Mutex::new(Vec::new()));
    let source_chunk_len = arrival_nodes.len();
    let threaded_sources = Arc::new(arrival_nodes.clone());
    let mut handles = vec![];

    for x in 1..thread_num {
        let source = Arc::clone(&threaded_sources);
        let transfer_patterns = Arc::clone(&total_transfer_patterns);
        let handle = thread::spawn(move || {
            let src = source;
            for i in ((x - 1) * (source_chunk_len / (thread_num - 1)))
                ..(x * source_chunk_len / (thread_num - 1))
            {
                let (target, path, _) = src.get(i).unwrap();
                let mut transfers = Vec::new();
                transfers.push(*target);
                let mut previous_node: NodeId = *target;
                for &node in path {
                    if previous_node.node_type == NodeType::Departure
                        || previous_node.node_type == NodeType::Transfer
                            && node.node_type == NodeType::Transfer
                    {
                        transfers.push(node);
                    }
                    previous_node = node;
                }

                transfers.reverse();
                transfers.shrink_to_fit();

                transfer_patterns.lock().unwrap().push(transfers);
                transfer_patterns.lock().unwrap().shrink_to_fit();
            }
        });

        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    let lock = Arc::try_unwrap(total_transfer_patterns).expect("failed to move out of arc");
    println!("found transfers {:?}", now.elapsed());
    let now = Instant::now();
    (lock, now)
}

// Arrival chain algo: For each arrival node, see if cost can be improved
// by simply waiting from an earlier arrival time. (favors less travel time)
pub fn arrival_loop(arrival_nodes: &mut [(NodeId, Vec<NodeId>, u64)]) {
    arrival_nodes.sort_unstable_by(|a, b| a.0.station_id.cmp(&b.0.station_id));
    let time_chunks = arrival_nodes.chunk_by_mut(|a, b| a.0.station_id <= b.0.station_id);
    for chunk in time_chunks {
        chunk.sort_unstable_by(|a, b| a.0.time.cmp(&b.0.time));
        let mut previous_arrival: Option<(NodeId, u64)> = None;
        for (node, path, cost) in chunk.iter_mut() {
            if let Some((prev_node, prev_cost)) = previous_arrival {
                let new_cost = prev_cost + (node.time.unwrap() - prev_node.time.unwrap());
                if new_cost <= *cost {
                    *cost = new_cost;
                    path.insert(1, prev_node);
                }
            }
            previous_arrival = Some((*node, *cost));
        }
        //new_arrival_list.append(&mut chunk.to_vec().to_owned())
    }
    //new_arrival_list
}

pub fn make_points_from_coords(
    source_lat: f64,
    source_lon: f64,
    target_lat: f64,
    target_lon: f64,
) -> (Point, Point) {
    let source = point!(x: source_lon, y:source_lat);
    let target = point!(x: target_lon, y:target_lat);
    (source, target)
}

#[derive(Serialize, Deserialize, Debug)]
pub struct QueryGraphItem {
    source: Point,
    target: Point,
    pub graph: Graph<NodeId, u8>,
    source_stations: Vec<Station>,
    target_stations: Vec<Station>,
    hubs: HashSet<i64>,
    source_nodes: Vec<NodeId>,
    target_nodes: Vec<NodeId>,
    station_map: HashMap<String, Station>,
}

pub fn query_graph_construction_from_geodesic_points(
    router: &mut TransitDijkstra,
    source: Point,
    target: Point,
    start_time: u64,
    hub_time_lim: u64,
    preset_distance: f64, //in meters
) -> QueryGraphItem {
    let now = Instant::now();
    //compute sets of N(source) and N(target) of stations N= near
    let (source_stations, nodes_per_source): (Vec<_>, Vec<_>)=
    router
    .station_info
    .clone()
    .into_iter()
    .filter(|(station, _)| {
        let node_coord = point!(x: station.lon as f64 / f64::powi(10.0, 14), y: station.lat as f64 / f64::powi(10.0, 14));
        Haversine::distance(source, node_coord) <= preset_distance
    })
    .unzip();

    println!(
        "Possible start nodes count: {}, t {:?}",
        source_stations.len(),
        now.elapsed()
    );
    let now = Instant::now();

    //let earliest_departure = sources.iter().min_by_key(|a| a.time).unwrap().time;

    let (target_stations, nodes_per_target): (Vec<_>, Vec<_>)=
    router
    .station_info
    .clone()
    .into_iter()
    .filter(|(station, _)| {
        let node_coord = point!(x: station.lon as f64 / f64::powi(10.0, 14), y: station.lat as f64 / f64::powi(10.0, 14));
        Haversine::distance(target, node_coord) <= preset_distance
    })
    .unzip();

    println!(
        "Possible end nodes count: {}, t {:?}",
        target_stations.len(),
        now.elapsed()
    );
    let now = Instant::now();

    //get hubs of important stations I(hubs)
    let hubs = hub_selection(router, 50000, hub_time_lim, router.station_map.len()); //cost limit at 10 hours, arbitrary

    println!("hubs: {:?}, t {:?}", &hubs, now.elapsed());

    let mut tps = Vec::new();
    
    let thread_num = 8; //8 for local searches

    for source in source_stations.iter() {
        let now = Instant::now();
        let (l_tps, n_now) =
            num_transfer_patterns_from_source(source.id, router, Some(&hubs), Some(start_time), thread_num);
        println!(
            "local tp {:?} or immediate {:?}",
            now.elapsed(),
            n_now.elapsed()
        );

        let now = Instant::now();
        tps.extend(l_tps.lock().unwrap().drain(..));
        println!("extending local {:?}", now.elapsed());
    }

    let now = Instant::now();
    let reached: Vec<_> = tps.iter().map(|t| t.last().unwrap().station_id).collect();
    let used_hubs: Vec<_> = hubs.clone().into_iter().filter(|n| reached.contains(n)).collect();

    //global transfer patterns from I(hubs) to to N(target())
    println!("num hubs used {:?}, t {:?}", used_hubs, now.elapsed());

    /*for hub in used_hubs.iter() {
        let now = Instant::now();
        let (g_tps, n_now) =
            num_transfer_patterns_from_source(**hub, router, None, Some(start_time));
        println!(
            "ran tp for hubs {:?} vs immediate {:?}",
            now.elapsed(),
            n_now.elapsed()
        );

        let now = Instant::now();
        tps.extend(g_tps.lock().unwrap().drain(..));
        println!("extending hubs {:?}", now.elapsed());
    }*/

    
    let total_transfer_patterns = Arc::new(Mutex::new(tps));

    let num_used_hubs = used_hubs.len();

    let thread_num = 2.max(num_used_hubs / 2);

    let threaded_roots = Arc::new(used_hubs);
    let arc_router = Arc::new(router.clone());
    let mut handles = vec![];

    for x in 1..thread_num + 1 {
        let roots = Arc::clone(&threaded_roots);
        let transfer_patterns = Arc::clone(&total_transfer_patterns);
        let router = Arc::clone(&arc_router);
        let handle = thread::spawn(move || {
            let r = roots;
            for i in ((x - 1) * (num_used_hubs / (thread_num - 1)))
                ..(x * num_used_hubs / (thread_num - 1))
            {
                let now = Instant::now();
                let hub = r.get(i).unwrap();
                let (g_tps, n_now) =
                    num_transfer_patterns_from_source(*hub, &router, None, Some(start_time), 6);
                println!(
                    "ran tp for hubs {:?} vs immediate {:?}",
                    now.elapsed(),
                    n_now.elapsed()
                );

                let mut ttp = transfer_patterns.lock().unwrap();
                ttp.extend(g_tps.lock().unwrap().drain(..));
                println!("extending hubs {:?}", now.elapsed());
            }
        });

        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    let tps = total_transfer_patterns.lock().unwrap();
    println!("source to hub tps num {}", tps.len());
    

    let now = Instant::now();

    let source_nodes: Vec<_> = nodes_per_source
        .into_iter()
        .flat_map(|x| {
            x.into_iter()
                .map(|(a, b, _)| (a, b))
                .unzip::<u64, NodeId, Vec<u64>, Vec<NodeId>>()
                .1
        })
        .filter(|node| node.time >= Some(start_time) && node.time <= Some(start_time + 3600))
        .collect();

    let earliest_departure = source_nodes.iter().min_by_key(|a| a.time).unwrap().time;

    let target_nodes: Vec<_> = nodes_per_target
        .into_iter()
        .flat_map(|x| {
            x.into_iter()
                .map(|(a, b, _)| (a, b))
                .unzip::<u64, NodeId, Vec<u64>, Vec<NodeId>>()
                .1
        })
        .filter(|node| {
            node.time >= earliest_departure && node.time <= Some(earliest_departure.unwrap() + 3600)
            //how long you're willing to wait
        })
        .collect();

    let paths = tps
        .iter()
        .filter(|v| {
            source_nodes.contains(v.first().unwrap()) || target_nodes.contains(v.last().unwrap())
        })
        .collect::<Vec<_>>();

    println!("paths {:?}", now.elapsed());

    let now = Instant::now();

    let mut graph: Graph<NodeId, u8> = Graph::new(); //tail, heads

    for path in paths.iter() {
        let mut prev = None;
        for node in path.iter() {
            let head = graph.add_node(*node);
            if let Some(prev) = prev {
                graph.add_edge(prev, head, 1);
            }
            prev = Some(head);
        }
    }

    println!("collecting paths {:?}", now.elapsed());

    QueryGraphItem {
        source,
        target,
        graph,
        source_stations,
        target_stations,
        hubs,
        source_nodes,
        target_nodes,
        station_map: router.station_map.clone(),
    }
}

pub fn query_graph_search(
    //roads: &RoadNetwork,
    connections: DirectConnections,
    query_info: QueryGraphItem,
) -> Option<(NodeId, PathedNode)> {
    /*let mut source_paths: HashMap<i64, _> = HashMap::new();

    let road_node_tree = RTree::bulk_load(
        roads
            .nodes
            .values()
            .map(|n| int_to_coord(n.lon, n.lat))
            .collect(),
    );

    println!("Made rtree");

    let mut graph = RoadDijkstra::new(roads);

    println!("Made graph of road dijkstras");

    if let Some(start_road_node) = road_node_tree.nearest_neighbor(&(query_info.source.0.x_y())) {
        for source in query_info.source_stations.iter() {
            if let Some(station_sought) =
                road_node_tree.nearest_neighbor(&int_to_coord(source.lon, source.lat))
            {
                let road_source = *roads
                    .nodes_by_coords
                    .get(&coord_to_int(start_road_node.0, start_road_node.1))
                    .unwrap();
                let station = *roads
                    .nodes_by_coords
                    .get(&coord_to_int(station_sought.0, station_sought.1))
                    .unwrap();

                //if let Some(result) = graph.dijkstra(road_source, station) { //figure this out later, use Valhalla OSM
                let result = 0;
                    source_paths.insert(source.id, result);
                //}
            }
        }
    }

    println!("source paths {:?}", source_paths.keys());

    let mut target_paths: HashMap<i64, _> = HashMap::new();

    if let Some(end_road_node) = road_node_tree.nearest_neighbor(&(query_info.target.0.x_y())) {
        for target in query_info.target_stations.iter() {
            if let Some(station_sought) =
                road_node_tree.nearest_neighbor(&int_to_coord(target.lon, target.lat))
            {
                let road_target = *roads
                    .nodes_by_coords
                    .get(&coord_to_int(end_road_node.0, end_road_node.1))
                    .unwrap();
                let station = *roads
                    .nodes_by_coords
                    .get(&coord_to_int(station_sought.0, station_sought.1))
                    .unwrap();
                //if let Some(result) = graph.dijkstra(station, road_target) { //figure this out later, use Valhalla OSM
                let result = 0;
                    target_paths.insert(target.id, result);
                //}
            }
        }
    }

    println!("targ paths {:?}", target_paths.keys());
    */

    let mut min_cost = 0;
    let mut router = TDDijkstra::new(connections, query_info.graph);

    let mut returned_val: Option<(NodeId, PathedNode)> = None; //source, target, path

    for source_id in query_info.source_nodes.iter() {
        //if let Some(_source_path) = source_paths.get(&source_id.station_id){
        //println!("s {:?}", source_id.station_id);
        //if let Some(_target_path) = target_paths.get(&target_id.station_id){
        //println!("t {:?}", target_id.station_id);
        let path = router.time_dependent_dijkstra(*source_id, &query_info.target_nodes);
        if let Some(transit_path) = path {
            let new_cost = transit_path.cost_from_start;
            //+ source_path.distance_from_start
            //+ target_path.distance_from_start;
            if new_cost > min_cost {
                min_cost = new_cost;
                returned_val = Some((*source_id, transit_path));
            }
        }
    }
    returned_val
}
