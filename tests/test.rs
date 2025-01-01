//use geo::point;
//use std::collections::HashMap;
//use std::collections::HashSet;
//use std::env;
//use std::f64::consts;
use std::fs::*;
use std::io::BufReader;
//use std::io::Write;
use std::time::Instant;
//use transit_router::coord_int_convert::coord_to_int;
//use transit_router::NodeType;
//use transit_router::RoadNetwork;
use transit_router::{transfer_patterns::*, transit_network::*};

#[test]
fn test() {
    let savepath = "results.json";

    println!("generating transit network graph");
    let gtfs = read_from_gtfs_zip("ctt.zip");
    let trips = gtfs.trips.clone();
    let routes = gtfs.routes.clone();
    let stops = gtfs.stops.clone();
    let (mut router, connections) = new_transit_network(gtfs, "Wednesday".to_string(), 0);

    //full routing test
    //see following link, anything but first option (which includes walking between stations, hasnt been implemented yet)
    //https://www.google.com/maps/dir/Bloomfield,+Connecticut+06002/77+Forest+St,+Hartford,+CT+06105/@41.823207,-72.7745391,34082m/data=!3m1!1e3!4m20!4m19!1m5!1m1!1s0x89e7001af40714d7:0xc4be608b22d7e4a8!2m2!1d-72.7197095!2d41.8683576!1m5!1m1!1s0x89e653502e880197:0xc1f0096f7d179457!2m2!1d-72.7005256!2d41.7671825!2m4!4e3!6e0!7e2!8j1727241000!3e3!5i1

    let preset_distance = 250.0;

    //pepperidge farm to harriet beecher stowe center
    let (source, target) = make_points_from_coords(
        41.86829675142084,
        -72.71973332600558,
        41.76726348091365,
        -72.70049435551549,
    );

    let now = Instant::now();
    let graph = query_graph_construction_from_geodesic_points(
        &mut router,
        source,
        target,
        18600, //5:10 AM
        86400, //24 hour searchspace
        preset_distance,
    );

    let output = File::create(savepath).unwrap();
    println!("query graph constructed in {:?}", now.elapsed());
    serde_json::to_writer(output, &graph).unwrap();

    //part 2

    let file = File::open(savepath).ok().unwrap();
    let reader = BufReader::new(file);
    let graph: QueryGraphItem = serde_json::from_reader(reader).unwrap();

    //road network, for footpaths
    /*let now = Instant::now();
    println!("generating street network graph");
    let path = "ct.pbf";
    let data = RoadNetwork::read_from_osm_file(path).unwrap();
    let mut roads = RoadNetwork::new(data.0, data.1);
    //roads = roads.reduce_to_largest_connected_component();

    println!("time for road {:?}", now.elapsed());

    println!("# of nodes: {}", roads.nodes.len());
    println!(
        "# of edges: {}",
        roads.edges.values().map(|edges| edges.len()).sum::<usize>()
    );
    let run_query = query_graph_search(&roads, connections, graph);
    */

    let run_query = query_graph_search(connections, graph);

    if let Some(stuff) = run_query {
        let path = stuff.1.get_tp(&trips);
        for (node, route) in path.0 {
            println!("{:?}", node);
            if let Some(route) = route {
                println!(
                    "via {:?}",
                    //stops.get(&node.station_id.to_string()).unwrap(),
                    routes.get(&route).unwrap().short_name
                );
            } else {
                println!("start {}", stops.get(&node.station_id.to_string()).unwrap());
            }
        }
    } else {
        println!("no path");
    }

}

//connection tests, these should be valid transfers --> success!
/*fn connections() {
    //https://maps.app.goo.gl/eXf4S5edPM8vgvVt9
    println!("time for transit {:?}", now.elapsed());
    let start_station = *transit_graph.station_map.get("9079").unwrap(); //Blue Hills Ave @ Home Goods
    let end_station = *transit_graph.station_map.get("1682").unwrap(); //Bloomfield Ave @ Advo

    let x = direct_connection_query(&connections, start_station, end_station, 25680); //7:08 AM
    let y = direct_connection_query(&connections, 9079, 1682, 25680); //7:08 AM
    println!("dc query {:?} and {:?}", x, y);

    //https://maps.app.goo.gl/szffQJAEALqSeHNF7
    let source_id = NodeId {
        //Downtown New Britain Station @ Columbus Blvd Bay
        node_type: NodeType::Arrival,
        station_id: 13381,
        time: Some(19200), //5:20 AM, 10 second transfer buffer
        trip_id: 1758411,
    };
    let target_id = NodeId {
        //Hart St @ Camp St
        node_type: NodeType::Arrival,
        station_id: 9738,
        time: Some(19515),
        trip_id: 1758411,
    };
    let now = Instant::now();
    let d = router.time_expanded_dijkstra(vec![source_id], None);
    println!("time for dijkstra {:?}", now.elapsed());

    let r = d.get(&target_id).unwrap().clone().get_path();
    println!("routing {:#?} and visted count {}", r.1, d.len());

    let mut test_node: NodeId = serde_json::from_str("\"Arrival,9079,19440,1752373\"").unwrap();
    println!("test node {:?}", test_node)


    //early stage Direct-Connection Query Test
    /*let connections = DirectConnections {
        route_tables: HashMap::from([("L17".to_string(), LineConnectionTable {
            times_from_start: HashMap::from([(154,0), (97,420), (987, 720), (111,1260)]),
            start_times: Vec::from([29700, 33300, 36900, 40800, 44400])
        })]),
        lines_per_station: HashMap::from([(97, Vec::from([
                ("L8".to_string(), 4), ("L17".to_string(), 2),("L34".to_string(), 5), ("L87".to_string(), 17)])),
            (111, Vec::from([
                ("L9".to_string(), 1), ("L13".to_string(), 5),("L17".to_string(), 4), ("L55".to_string(), 16)
            ]))])
    };
    let query = direct_connection_query(&   connections, 97, 111, 37200);
    println!("aa query results: {:?}", query);*/
}*/

//Pareto-se t ordering
/*fn pareto_recompute(set: &mut Vec<(i32, i32)>, c_p: (i32, i32)) {
    set.sort_by_key(|(x, y)| if y != &0 { 10 * x + (10 / y) } else { 10 * x });
    let mut incomparable = true;
    for c in set.iter() {
        if (c.0 <= c_p.0 && c.1 <= c_p.1) || (c.0 >= c_p.0 && c.1 >= c_p.1) {
            incomparable = false;
        }

    }
    if incomparable {
        set.push(c_p);
        set.dedup();
        set.sort_by_key(|(x, y)| if y != &0 { 10 * x + (10 / y) } else { 10 * x });
    }
}

let mut set = vec![(1, 5), (7, 1), (2, 4), (4, 3)];
pareto_recompute(&mut set, (6, 2));
println!("{:?}", set);
pareto_recompute(&mut set, (1, 1));
println!("{:?}", set);
pareto_recompute(&mut set, (8, 0));
println!("{:?}", set);
pareto_recompute(&mut set, (8, 0));
println!("{:?}\n", set);

let mut set = vec![(9, 1), (8, 1), (2, 7), (3, 3), (6, 4), (1, 9)];
pareto_recompute(&mut set, (5, 5));
println!("{:?}", set);
pareto_recompute(&mut set, (7, 3));
println!("{:?}", set);
pareto_recompute(&mut set, (7, 2));
println!("{:?}", set);
*/