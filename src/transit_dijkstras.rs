//transit_dijkstras algorithms and helper functiions
use crate::transit_network::*;
use crate::NodeType;
use gtfs_structures::Trip;
use petgraph::Direction::Outgoing;
use rand::Rng;
use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap, HashSet};
use std::rc::Rc;
use petgraph::{graph::*, visit::EdgeRef};

#[derive(Debug, PartialEq, Clone, Eq, PartialOrd, Ord, Hash)]
pub struct PathedNode {
    //node that references parent nodes, used to create path from goal node to start node
    pub self_id: NodeId,
    pub graph_index: NodeIndex,
    pub cost_from_start: u64,
    pub parent_node: Option<Rc<PathedNode>>,
    pub transfer_count: u8,
}

impl PathedNode {
    pub fn new(self_id: NodeId, graph_index: NodeIndex) -> PathedNode {
        PathedNode {
            self_id,
            graph_index,
            cost_from_start: 0,
            parent_node: None,
            transfer_count: 0,
        }
    }

    pub fn get_path(self) -> (Vec<NodeId>, u64) {
        //path, cost
        //uses reference to find the source node with parent_node == None
        //vec.get(0) = target node
        let mut shortest_path = Vec::new();
        let total_distance: u64 = self.cost_from_start;
        let mut current_path = &Some(Rc::new(self));
        while let Some(current) = current_path {
            shortest_path.push(current.self_id); //current.self_id
            current_path = &current.parent_node; //current = current.parent_node
        }
        //shortest_path.push(current_path.unwrap()));
        (shortest_path, total_distance)
    }

    pub fn get_tp(self, trips: &HashMap<String, Trip>) -> (Vec<(NodeId, Option<String>)>, u64) {
        let mut tp = Vec::new();
        let journey_cost: u64 = self.cost_from_start;
        let mut current_path = &Some(Rc::new(self));
        let mut prev_node: Option<NodeId> = None;
        let mut prev_route: Option<String> = None;
        while let Some(current) = current_path {
            let node = current.self_id;
            let route = current.get_route(trips);
            current_path = &current.parent_node;

            if let Some(prev) = prev_node {
                if prev.trip_id != node.trip_id && prev_route != route
                //&& !(prev.node_type == NodeType::Transfer && prev.station_id == node.station_id)
                {
                    tp.push((node, route.to_owned()));
                }
            } else {
                tp.push((node, route.to_owned()));
            }

            prev_route = route;
            prev_node = Some(node);
        }
        tp.reverse();
        (tp, journey_cost)
    }

    pub fn get_route(&self, trips: &HashMap<String, Trip>) -> Option<String> {
        let trip_id = self.self_id.trip_id.to_string();
        let try_trip = trips.get(&trip_id);
        if let Some(trip) = try_trip {
            return Some(trip.route_id.clone());
        }
        None
    }
}

#[derive(Debug, Clone)]
pub struct TransitDijkstra {
    //handle time expanded dijkstra calculations
    pub graph: Graph<NodeId, u64>,
    pub station_map: HashMap<String, Station>,
    pub station_info: HashMap<Station, Vec<(u64, NodeId, NodeIndex)>>,
    cost_upper_bound: u64,
}

impl TransitDijkstra {
    //implementation of time expanded dijkstra's shortest path algorithm
    pub fn new(graph: &Graph<NodeId, u64>, station_map: HashMap<String, Station>, station_info: HashMap<Station, Vec<(u64, NodeId, NodeIndex)>>) -> Self {
        Self {
            graph: graph.clone(),
            cost_upper_bound: u64::MAX,
            station_map,
            station_info
        }
    }

    pub fn set_cost_upper_bound(&mut self, upper_bound: u64) {
        self.cost_upper_bound = upper_bound;
    }

    pub fn get_neighbors(
        &self,
        current: &PathedNode,
        visited_nodes: &HashMap<NodeIndex, PathedNode>,
    ) -> Vec<(NodeIndex, u64)> {
        //return node id of neighbors
        let mut paths = Vec::new();
        for next_node_index in self.graph.edges_directed(current.graph_index, Outgoing) {
            let head = next_node_index.target();
            if visited_nodes.contains_key(&head) {
                continue;
            }

            paths.push((head, *next_node_index.weight()));
        }
        paths
    }

    pub fn time_expanded_dijkstra(
        &self,
        source_id_set: Vec<NodeId>,
        hubs: Option<&HashSet<i64>>,
    ) -> HashMap<NodeIndex, PathedNode> {
        //path, visted nodes, transfer count
        //returns path from the source to target if exists, also path from every node to source
        //Heap(distance, node), Reverse turns binaryheap into minheap (default is maxheap)

        let mut priority_queue: BinaryHeap<Reverse<(u64, PathedNode)>> = BinaryHeap::new();
        let mut visited_nodes: HashMap<NodeIndex, PathedNode> = HashMap::new();
        //let mut inactive_nodes: HashSet<NodeIndex> = HashSet::new();

        //stores distances of node relative to target
        let mut gscore: HashMap<NodeIndex, u64> = HashMap::new();
        for self_id in source_id_set {
            let graph_index = self.graph.node_indices().find(|i| self.graph[*i] == self_id).unwrap();
            let source_node = PathedNode::new(self_id, graph_index);
            gscore.insert(graph_index, 0);
            priority_queue.push(Reverse((0, source_node)));
        }
        let mut current_cost;

        while !priority_queue.is_empty() {
            let pathed_current_node = priority_queue.pop().unwrap().0 .1; //.0 "unwraps" from Reverse()
            current_cost = pathed_current_node.cost_from_start;
            let idx = pathed_current_node.graph_index;
            visited_nodes.insert(idx, pathed_current_node.clone());

            /*//stop for local TP when all unsettled nodes are inactive --> unvisited nodes are subset of inactive nodes
            //don't need this with 3-legs heuristic
            if hubs.is_some() {
                let a = visited_nodes.keys().collect::<HashSet<_>>();
                let b = inactive_nodes.iter().collect();
                let c = a.union(&b);
                if self.graph.nodes.len() == c.count() {
                    println!("augh");
                    return visited_nodes;
                }
            }
            */

            //stop conditions
            //cost or # of settled nodes goes over limit
            if current_cost > self.cost_upper_bound {
                println!("cost over");
                return visited_nodes;
            }

            //cost is higher than current path (not optimal)
            if current_cost > *gscore.get(&idx).unwrap_or(&u64::MAX) {
                continue;
            }

            let neighbors = self.get_neighbors(&pathed_current_node, &visited_nodes);

            for neighbor in neighbors {
                let neighbor_node_id = self.graph.node_weight(neighbor.0).unwrap();
                let mut transfer_count = pathed_current_node.transfer_count;
                if pathed_current_node.self_id.node_type == NodeType::Transfer
                    //&& neighbor.0.node_type == NodeType::Arrival
                    && neighbor_node_id.node_type == NodeType::Departure
                {
                    //transfer arc detected, increment transfer count for current path
                    transfer_count += 1;

                    //limit local search to at most 2 transfers for 3-legs heuristic
                    if transfer_count > 2 && hubs.is_some() {
                        continue;
                    }
                }

                let temp_distance = current_cost + neighbor.1;
                let next_distance = *gscore.get(&neighbor.0).unwrap_or(&u64::MAX);

                if temp_distance < next_distance {
                    gscore.insert(neighbor.0, temp_distance);
                    let prev_node: Rc<PathedNode> = Rc::new(pathed_current_node.clone());

                    let tentative_new_node = PathedNode {
                        self_id: *neighbor_node_id,
                        graph_index: neighbor.0,
                        cost_from_start: temp_distance,
                        parent_node: Some(prev_node),
                        transfer_count,
                    };

                    priority_queue.push(Reverse((temp_distance, tentative_new_node)));
                }
            }
        }
        //println!("no path exists");
        visited_nodes
    }

    pub fn get_random_node_id(&self) -> Option<NodeIndex> {
        //returns ID of a random valid node from a graph
        let full_node_list = self.graph.node_indices().collect::<Vec<_>>();
        let mut rng = rand::thread_rng();
        let random: usize = rng.gen_range(0..full_node_list.len());
        full_node_list.get(random).copied()
    }
}
#[derive(Debug, Clone)]
pub struct TDDijkstra {
    //handle time dependent dijkstra calculations
    pub connections: DirectConnections,
    pub graph: Graph<NodeId, u8>,
    pub visited_nodes: HashMap<NodeIndex, PathedNode>,
}

impl TDDijkstra {
    //implementation of time dependent shortest path algorithm
    pub fn new(
        connections: DirectConnections,
        graph: Graph<NodeId, u8>,
    ) -> Self {
        let visited_nodes = HashMap::new();
        Self {
            connections,
            graph,
            visited_nodes,
        }
    }

    pub fn get_neighbors(
        &self,
        current: &PathedNode,
        connections: &DirectConnections,
    ) -> Vec<(NodeIndex, NodeId, u64)> {
        //return node id of neighbors
        let mut paths = Vec::new();
        for next_node_index in self.graph.edges_directed(current.graph_index, Outgoing) {
            let head_idx = next_node_index.target();

            if self.visited_nodes.contains_key(&head_idx) {
                continue;
            }

            let head_node = self.graph.node_weight(head_idx).unwrap();
            if let Some((dept, arr)) = direct_connection_query(
                connections,
                current.self_id.station_id,
                head_node.station_id,
                current.self_id.time.unwrap(),
            ) {
                let cost = arr - dept;
                paths.push((head_idx, *head_node, cost));
            }
        }
        paths
    }

    pub fn time_dependent_dijkstra(
        &mut self,
        source_id: NodeId,
        target_id: &[NodeId], //if target == None, settles all reachable nodes
    ) -> Option<PathedNode> {
        //returns path from the source to target if exists, also path from every node to source
        //Heap(distance, node), Reverse turns binaryheap into minheap (default is maxheap)

        let mut priority_queue: BinaryHeap<Reverse<(u64, PathedNode)>> = BinaryHeap::new();

        //stores distances of node relative to target
        let mut gscore: HashMap<NodeIndex, u64> = HashMap::new();

        self.visited_nodes.clear();

        let mut current_cost;

        let graph_index = self.graph.node_indices().find(|i| self.graph[*i] == source_id).unwrap();
        let source_node = PathedNode::new(source_id, graph_index);

        gscore.insert(graph_index, 0);

        priority_queue.push(Reverse((0, source_node)));

        while !priority_queue.is_empty() {
            let pathed_current_node = priority_queue.pop().unwrap().0 .1;
            current_cost = pathed_current_node.cost_from_start;

            if target_id.contains(&pathed_current_node.self_id) {
                return Some(pathed_current_node);
            }

            let idx = pathed_current_node.graph_index;

            self.visited_nodes.insert(idx, pathed_current_node.clone());

            //found target node

            //cost is higher than current path (not optimal)
            if current_cost > *gscore.get(&idx).unwrap_or(&u64::MAX) {
                continue;
            }

            for (neighbor_index, neighbor_node, neighbor_cost) in
                self.get_neighbors(&pathed_current_node, &self.connections)
            {
                let temp_distance = current_cost + neighbor_cost;
                let next_distance = *gscore.get(&neighbor_index).unwrap_or(&u64::MAX);

                if temp_distance < next_distance {
                    gscore.insert(neighbor_index, temp_distance);
                    let prev_node: Rc<PathedNode> = Rc::new(pathed_current_node.clone());
                    let tentative_new_node = PathedNode {
                        self_id: neighbor_node,
                        graph_index: neighbor_index,
                        cost_from_start: temp_distance,
                        parent_node: Some(prev_node),
                        transfer_count: 0,
                    };

                    priority_queue.push(Reverse((temp_distance, tentative_new_node.clone())));
                }
            }
        }
        None //(None, node_path_tracker)
    }
}
