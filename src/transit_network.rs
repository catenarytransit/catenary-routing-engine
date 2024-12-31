//constructs and preprocesses the graph struct from OSM data
use crate::coord_int_convert::coord_to_int;
use gtfs_structures::*;
use serde::{Deserialize, Serialize};
use serde_with::*;

use crate::NodeType;
use chrono::prelude::*;
use std::collections::hash_map::Entry;
use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
};

#[derive(Debug, PartialEq, Hash, Eq, Clone, Copy, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(into = "String")]
#[serde(from = "String")]
pub struct NodeId {
    //0 = "untyped"    1 = "arrival"   2 = "transfer"  3 = "departure"
    pub node_type: NodeType,
    pub station_id: i64,
    pub time: Option<u64>,
    pub trip_id: u64,
}

impl From<String> for NodeId {
    fn from(read_val: String) -> Self {
        let v: Vec<&str> = read_val.rsplit(',').collect();

        //reads the vec backwards, v is ["trip_id", "time", "station", "type"]
        NodeId {
            node_type: (*v.get(3).unwrap_or(&"")).to_string().into(),
            station_id: (*v.get(2).unwrap_or(&"")).parse().unwrap_or(0),
            time: (*v.get(1).unwrap_or(&"")).parse().ok(),
            trip_id: (*v.first().unwrap_or(&"")).parse().unwrap_or(0),
        }
    }
}

impl From<NodeId> for String {
    fn from(val: NodeId) -> Self {
        format!(
            "{},{},{},{}",
            <crate::common_enums::NodeType as std::convert::Into<String>>::into(val.node_type),
            val.station_id,
            val.time.unwrap_or(0),
            val.trip_id
        )
    }
}

#[derive(Debug, PartialEq, Hash, Eq, Clone, PartialOrd, Ord, Serialize, Deserialize)]
pub struct StationInfo {
    pub id: i64,
    pub lat: i64, //f64 * f64::powi(10.0, 14) as i64
    pub lon: i64, //f64 * f64::powi(10.0, 14) as i64
}

pub fn read_from_gtfs_zip(path: &str) -> Gtfs {
    let gtfs = gtfs_structures::GtfsReader::default()
        .read_shapes(false) // Won’t read shapes to save time and memory
        .read(path)
        .ok();
    gtfs.unwrap()
}

pub fn calendar_date_filter(
    given_weekday: &str,
    service_id: &str,
    calendar: &Calendar,
) -> Option<String> {
    let day_is_valid = match given_weekday {
        "monday" => calendar.monday,
        "tuesday" => calendar.tuesday,
        "wednesday" => calendar.wednesday,
        "thursday" => calendar.thursday,
        "friday" => calendar.friday,
        "saturday" => calendar.saturday,
        "sunday" => calendar.saturday,
        _ => false,
    };

    let local = Local::now().date_naive();

    if day_is_valid && local >= calendar.start_date && local <= calendar.end_date {
        Some(service_id.to_owned())
    } else {
        None
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct TimeExpandedGraph {
    //graph struct that will be used to route
    pub nodes: HashSet<NodeId>,
    pub edges: HashMap<NodeId, HashMap<NodeId, u64>>, // tail.id, <head.id, cost>
    pub station_map: HashMap<String, i64>, //station_id string, internal station_id (assigned number)
    pub station_info: HashMap<i64, (StationInfo, Vec<(u64, NodeId)>)>, //station_id, <cost, node>
}

#[derive(Debug, PartialEq, Clone)]
pub struct LineConnectionTable {
    //for a single line/route, gives the following information:
    pub times_from_start: HashMap<i64, u64>, //<stationid, time from start> for every station along the line/route
    pub start_times: Vec<u64>, //start times for vehicle from first station of this line
}

#[derive(Debug, PartialEq, Clone)]
pub struct DirectConnections {
    //helps find quick transfers between two different lines/routes by matching the station where two lines intersect --> used by Direct Connection Query
    pub route_tables: HashMap<String, LineConnectionTable>, //route_id, table
    pub lines_per_station: HashMap<i64, Vec<(String, u16)>>, //<stationid, <routeid, stop sequence number>> //gives lines operating at this station
}

//init new transit network graph based on results from reading GTFS zip
impl TimeExpandedGraph {
    pub fn new(
        mut gtfs: Gtfs,
        mut day_of_week: String,
        transfer_buffer: u64,
    ) -> (Self, DirectConnections) {
        day_of_week = day_of_week.to_lowercase();

        let mut nodes: HashSet<NodeId> = HashSet::new(); //maps GTFS stop id string to sequential numeric stop id
        let mut edges: HashMap<NodeId, HashMap<NodeId, u64>> = HashMap::new();
        let mut station_map: HashMap<String, i64> = HashMap::new();
        let mut station_info: HashMap<i64, (StationInfo, Vec<(u64, NodeId)>)> = HashMap::new(); // <stationid, (time, node_id)>, # of stations and # of times

        let mut route_tables: HashMap<String, LineConnectionTable> = HashMap::new();
        let mut lines_per_station: HashMap<i64, Vec<(String, u16)>> = HashMap::new();

        let service_ids_of_given_day: HashSet<String> = gtfs
            .calendar
            .iter()
            .filter_map(|(service_id, calendar)| {
                calendar_date_filter(day_of_week.as_str(), service_id, calendar)
            })
            .collect();

        let trip_ids_of_given_day: HashSet<String> = gtfs
            .trips
            .iter()
            .filter(|(_, trip)| service_ids_of_given_day.contains(&trip.service_id))
            .map(|(trip_id, _)| trip_id.to_owned())
            .collect();

        for (iterator, stop_id) in (0_i64..).zip(gtfs.stops.iter()) {
            station_map.insert(stop_id.0.clone(), stop_id.0.parse().unwrap_or(iterator));
        }

        let mut custom_trip_id: u64 = 0; //custom counter like with stop_id
        let mut nodes_by_time: Vec<(u64, NodeId)> = Vec::new();

        for (_, trip) in gtfs.trips.iter_mut() {
            if !trip_ids_of_given_day.contains(&trip.id) {
                continue;
            }

            let trip_id: u64 = trip.id.parse().unwrap_or({
                custom_trip_id += 1;
                custom_trip_id
            });

            trip.stop_times
                .sort_by(|a, b| a.stop_sequence.cmp(&b.stop_sequence));

            let trip_start_time: u64 = trip
                .stop_times
                .first()
                .unwrap()
                .arrival_time
                .unwrap()
                .into();
            let mut stations_time_from_trip_start = HashMap::new();

            let route_id = &trip.route_id;

            let mut prev_stop: Option<(NodeId, u64)> = None;

            for stoptime in trip.stop_times.iter() {
                let id = *station_map.get(&stoptime.stop.id).unwrap();

                let (lon, lat) = coord_to_int(
                    stoptime.stop.longitude.unwrap(),
                    stoptime.stop.latitude.unwrap(),
                );

                let arrival_time: u64 = stoptime.arrival_time.unwrap().into();

                stations_time_from_trip_start.insert(id, arrival_time - trip_start_time);

                match lines_per_station.entry(id) {
                    Entry::Occupied(mut o) => {
                        let map = o.get_mut();
                        map.push((route_id.to_string(), stoptime.stop_sequence));
                    }
                    Entry::Vacant(v) => {
                        v.insert(vec![(route_id.to_string(), stoptime.stop_sequence)]);
                    }
                }

                let arrival_node = NodeId {
                    node_type: NodeType::Arrival,
                    station_id: id,
                    time: Some(arrival_time),
                    trip_id,
                };
                let transfer_node = NodeId {
                    node_type: NodeType::Transfer,
                    station_id: id,
                    time: Some(arrival_time + transfer_buffer),
                    trip_id,
                };
                //direct link to next nodeset for compacting graph

                nodes.insert(arrival_node);
                nodes.insert(transfer_node);

                if let Some((prev_dep, prev_dep_time)) = prev_stop {
                    edges //travelling arc (prev transfer to arrival of same route)
                        .entry(prev_dep) //tail
                        .and_modify(|inner| {
                            inner.insert(arrival_node, arrival_time - prev_dep_time);
                            //head
                        })
                        .or_insert({
                            let mut a = HashMap::new();
                            a.insert(arrival_node, arrival_time - prev_dep_time); //head
                            a
                        });
                }

                edges //alighting arc (arrival to next transfer of same route)
                    .entry(arrival_node) //tail
                    .and_modify(|inner| {
                        inner.insert(transfer_node, transfer_buffer);
                        //head
                    })
                    .or_insert({
                        let mut a = HashMap::new();
                        a.insert(transfer_node, transfer_buffer); //head
                        a
                    });

                let node_list = vec![
                    (arrival_time, arrival_node),
                    (arrival_time + transfer_buffer, transfer_node),
                ];

                nodes_by_time.extend(node_list.iter());

                station_info
                    .entry(id)
                    .and_modify(|inner| {
                        inner.1.extend(node_list.iter());
                        inner.0.id = id;
                        inner.0.lat = lat;
                        inner.0.lon = lon;
                    })
                    .or_insert((StationInfo { id, lat, lon }, node_list));

                prev_stop = Some((transfer_node, arrival_time + transfer_buffer));
            }

            match route_tables.entry(route_id.clone()) {
                Entry::Occupied(mut o) => {
                    let table = o.get_mut();
                    table
                        .times_from_start
                        .extend(stations_time_from_trip_start.iter());
                    table.start_times.push(trip_start_time);
                }
                Entry::Vacant(v) => {
                    v.insert(LineConnectionTable {
                        times_from_start: stations_time_from_trip_start,
                        start_times: Vec::from([trip_start_time]),
                    });
                }
            }
        }
        for (_, station) in station_info.iter_mut() {
            station.1.sort_by(|a, b| a.0.cmp(&b.0));
            let time_chunks = station.1.chunk_by_mut(|a, b| a.0 == b.0);

            let mut station_nodes_by_time: Vec<(u64, NodeId)> = Vec::new();
            for chunk in time_chunks {
                chunk.sort_by(|a, b| a.1.node_type.cmp(&b.1.node_type));
                station_nodes_by_time.append(&mut chunk.to_vec().to_owned())
            }

            for (current_index, node) in station_nodes_by_time.iter().enumerate() {
                if node.1.node_type == NodeType::Transfer {
                    for index in current_index + 1..station_nodes_by_time.len() {
                        let future_node = station_nodes_by_time.get(index).unwrap();
                        if future_node.1.node_type == NodeType::Transfer {
                            edges //waiting arc (transfer to transfers of any route)
                                .entry(node.1) //tail
                                .and_modify(|inner| {
                                    inner.insert(future_node.1, future_node.0 - node.0);
                                    //head
                                })
                                .or_insert({
                                    let mut a = HashMap::new();
                                    a.insert(future_node.1, future_node.0 - node.0); //head
                                    a
                                });
                        }
                    }
                }
            }
        }

        for (_, stop_sequence) in lines_per_station.iter_mut() {
            stop_sequence.sort();
            stop_sequence.dedup();
        }

        (
            Self {
                nodes,
                edges,
                station_map,
                station_info,
            },
            DirectConnections {
                route_tables,
                lines_per_station,
            },
        )
    }
}

//For each station: Hashmap<stationid, (line, stop sequence #)>
//Line struct: line_id, hashmap<station, time_from_start>, hashset<starttime>
//Given time and connection: find intersection of route of two stations where
//(station line start) > (station line end)
//find (first start time) after given time - (hashmap find start)
//compute arrival time from (first start time) + (hashmap find end)

pub fn direct_connection_query(
    connections: &DirectConnections,
    start_station: i64,
    end_station: i64,
    time: u64,
) -> Option<(u64, u64)> {
    //departure time from start, arrival time to end

    let start = connections.lines_per_station.get(&start_station).unwrap();
    let end = connections.lines_per_station.get(&end_station).unwrap();

    let mut route = "";
    for (s_route, s_seq) in start {
        for (e_route, e_seq) in end {
            if s_route == e_route && s_seq <= e_seq {
                route = s_route;
                break;
            }
        }
    }

    if route.is_empty() {
        println!("cant find lines per station");
    }

    if let Some(table) = connections.route_tables.get(route) {
        let mut start_times = table.start_times.clone();
        let time_to_start = table.times_from_start.get(&start_station).unwrap();
        let time_to_end = table.times_from_start.get(&end_station).unwrap();
        start_times.sort();
        if let Some(first_valid_start_time) =
            start_times.iter().find(|&&s| s > (time - time_to_start))
        {
            let departure = first_valid_start_time + time_to_start;
            let arrival = first_valid_start_time + time_to_end;
            Some((departure, arrival))
        } else {
            None
        }
    } else {
        println!("err ");
        None
    }
}
