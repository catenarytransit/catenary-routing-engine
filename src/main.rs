#![allow(unused)]
// Copyright Chelsea Wen
// Cleaned up somewhat by Kyler Chin
use serde_json::{Result, Value};
use std::fs::File;
use std::io::BufReader;
use transit_router::{transfer_patterns::*, transit_dijkstras::*, transit_network::*};
use std::time::Instant;

fn main() {
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