//transit_dijkstras algorithms and helper functiions
use crate::transit_network::*;
use crate::NodeType;
use gtfs_structures::Trip;
use rand::Rng;
use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap, HashSet};
use std::hash::Hash;
use std::rc::Rc;
use petgraph::graph::*;

#[derive(Debug, Clone)]
pub struct TransitDijkstra {
    //handle time expanded dijkstra calculations
    pub graph: Graph<NodeId, u64>,
    cost_upper_bound: u64,
}

#[derive(Debug, PartialEq, Clone, Eq, PartialOrd, Ord, Hash)]
pub struct PathedNode {
    //node that references parent nodes, used to create path from goal node to start node
    pub node_self: NodeId,
    pub cost_from_start: u64,
    pub parent_node: Option<Rc<PathedNode>>,
    pub transfer_count: u8,
}

impl PathedNode {
    pub fn new(id: NodeId) -> PathedNode {
        PathedNode {
            node_self: id,
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
            shortest_path.push(current.node_self); //current.node_self
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
            let node = current.node_self;
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
        let trip_id = self.node_self.trip_id.to_string();
        let try_trip = trips.get(&trip_id);
        if let Some(trip) = try_trip {
            return Some(trip.route_id.clone());
        }
        None
    }
}

impl TransitDijkstra {
    //implementation of time expanded dijkstra's shortest path algorithm
    pub fn new(graph: &Graph<NodeId, u64>) -> Self {
        Self {
            graph: graph.clone(),
            cost_upper_bound: u64::MAX,
        }
    }

    pub fn set_cost_upper_bound(&mut self, upper_bound: u64) {
        self.cost_upper_bound = upper_bound;
    }

    pub fn get_neighbors(
        &self,
        current: &PathedNode,
        visited_nodes: &HashMap<NodeId, PathedNode>,
    ) -> Vec<(NodeId, u64)> {
        //return node id of neighbors
        if let Some(connections) = self.graph.neighbors(&current.node_self) {
            for (next_node_id, cost) in connections {
                if visited_nodes.contains_key(next_node_id) {
                    continue;
                }

                paths.push((*next_node_id, *cost));
            }
        }
        paths
    }

    pub fn time_expanded_dijkstra(
        &self,
        source_id_set: Vec<NodeId>,
        hubs: Option<&HashSet<i64>>,
    ) -> HashMap<NodeId, PathedNode> {
        //path, visted nodes, transfer count
        //returns path from the source to target if exists, also path from every node to source
        //Heap(distance, node), Reverse turns binaryheap into minheap (default is maxheap)

        let mut priority_queue: BinaryHeap<Reverse<(u64, PathedNode)>> = BinaryHeap::new();
        let mut visited_nodes: HashMap<NodeId, PathedNode> = HashMap::new();
        let mut inactive_nodes: HashSet<NodeId> = HashSet::new();

        //stores distances of node relative to target
        let mut gscore: HashMap<NodeId, u64> = HashMap::new();
        for source_id in source_id_set {
            let source_node = PathedNode::new(source_id);
            gscore.insert(source_id, 0);
            priority_queue.push(Reverse((0, source_node)));
        }
        let mut current_cost;

        while !priority_queue.is_empty() {
            let pathed_current_node = priority_queue.pop().unwrap().0 .1; //.0 "unwraps" from Reverse()
            current_cost = pathed_current_node.cost_from_start;
            let idx = pathed_current_node.node_self;
            visited_nodes.insert(idx, pathed_current_node.clone());

            //stop search for local TP if all unsettled NodeIds are inactive -->
            //all unvisited nodes should become subset of inactive nodes
            //don't need this with 3-legs heuristic
            /*if hubs.is_some() {
                let a = visited_nodes.keys().collect::<HashSet<_>>();
                let b = inactive_nodes.iter().collect();
                let c = a.union(&b);
                if self.graph.nodes.len() == c.count() {
                    println!("augh");
                    return visited_nodes;
                }
            }*/

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

            if hubs.is_some_and(|a| a.contains(&pathed_current_node.node_self.station_id))
                && pathed_current_node.node_self.node_type == NodeType::Transfer
            {
                inactive_nodes.extend(neighbors.iter().map(|(node, _)| node));
            }

            for neighbor in neighbors {
                let mut transfer_count = pathed_current_node.transfer_count;
                if pathed_current_node.node_self.node_type == NodeType::Transfer
                    //&& neighbor.0.node_type == NodeType::Arrival
                    && neighbor.0.node_type == NodeType::Departure
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
                        node_self: neighbor.0,
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

    pub fn get_random_node_id(&self) -> Option<NodeId> {
        //returns ID of a random valid node from a graph
        let full_node_list = graph.nodes.iter().copied().collect::<Vec<NodeId>>();
        let mut rng = rand::thread_rng();
        let random: usize = rng.gen_range(0..full_node_list.len());
        full_node_list.get(random).copied()
    }

    /*pub fn get_random_start(&self) -> Option<NodeId> {
        //returns ID of a random valid node from a graph
        let full_node_list: Vec<_> = self
            .graph
            .nodes
            .iter()
            .filter(|id| {
                id.node_type == NodeType::Departure
                    && id.time > Some(21600)
                    && id.time < Some(75600)
            })
            .copied()
            .collect();
        let mut rng = rand::thread_rng();
        let random: usize = rng.gen_range(0..full_node_list.len());
        full_node_list.get(random).copied()
    }*/
}
#[derive(Debug, PartialEq, Clone)]
pub struct TDDijkstra {
    //handle time dependent dijkstra calculations
    pub connections: DirectConnections,
    pub edges: HashMap<NodeId, HashSet<NodeId>>,
    pub visited_nodes: HashMap<NodeId, PathedNode>,
    pub station_map: HashMap<String, i64>,
}

impl TDDijkstra {
    //implementation of time dependent shortest path algorithm
    pub fn new(
        connections: DirectConnections,
        edges: HashMap<NodeId, HashSet<NodeId>>,
        station_map: HashMap<String, i64>,
    ) -> Self {
        let visited_nodes = HashMap::new();
        Self {
            connections,
            edges,
            visited_nodes,
            station_map,
        }
    }

    pub fn get_neighbors(
        &self,
        current: &PathedNode,
        connections: &DirectConnections,
    ) -> Vec<(NodeId, u64)> {
        //return node id of neighbors
        let mut paths = Vec::new();
        let mut next_node_edges = HashMap::new();

        if let Some(arcs) = self.edges.get(&current.node_self) {
            for next_node in arcs {
                if let Some((dept, arr)) = direct_connection_query(
                    connections,
                    *self
                        .station_map
                        .get(&current.node_self.station_id.to_string())
                        .unwrap(),
                    *self
                        .station_map
                        .get(&next_node.station_id.to_string())
                        .unwrap(),
                    current.node_self.time.unwrap(),
                ) {
                    let cost = arr - dept;
                    next_node_edges.insert(next_node, cost);
                }
            }
        }
        for (next_node_id, cost) in next_node_edges {
            if self.visited_nodes.contains_key(next_node_id) {
                continue;
            }

            paths.push((*next_node_id, cost));
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
        let mut gscore: HashMap<NodeId, u64> = HashMap::new();

        self.visited_nodes.clear();

        let mut current_cost = 0;

        let source_node: PathedNode = PathedNode {
            node_self: (source_id),
            cost_from_start: current_cost,
            parent_node: (None),
            transfer_count: 0,
        };

        gscore.insert(source_id, 0);

        priority_queue.push(Reverse((0, source_node)));

        while !priority_queue.is_empty() {
            let pathed_current_node = priority_queue.pop().unwrap().0 .1;
            current_cost = pathed_current_node.cost_from_start;
            let idx = pathed_current_node.node_self;

            self.visited_nodes.insert(idx, pathed_current_node.clone());

            //found target node
            if target_id.contains(&idx) {
                return Some(pathed_current_node);
            }

            //cost is higher than current path (not optimal)
            if current_cost > *gscore.get(&idx).unwrap_or(&u64::MAX) {
                continue;
            }

            for (neighbor_node, neighbor_cost) in
                self.get_neighbors(&pathed_current_node, &self.connections)
            {
                let temp_distance = current_cost + neighbor_cost;
                let next_distance = *gscore.get(&neighbor_node).unwrap_or(&u64::MAX);

                if temp_distance < next_distance {
                    gscore.insert(neighbor_node, temp_distance);
                    let prev_node: Rc<PathedNode> = Rc::new(pathed_current_node.clone());
                    let tentative_new_node = PathedNode {
                        node_self: neighbor_node,
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
