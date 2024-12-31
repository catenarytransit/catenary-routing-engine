use serde::{Deserialize, Serialize};

#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Debug, Hash, Serialize, Deserialize)]
pub enum NodeType {
    Untyped = 0,
    Arrival = 1,
    Transfer = 2,
}

impl From<String> for NodeType {
    fn from(read_val: String) -> Self {
        match read_val.as_str() {
            "Untyped" => NodeType::Untyped,
            "Arrival" => NodeType::Arrival,
            "Transfer" => NodeType::Transfer,
            &_ => NodeType::Untyped,
        }
    }
}

impl From<NodeType> for String {
    fn from(v: NodeType) -> String {
        match v {
            NodeType::Untyped => "Untyped".to_string(),
            NodeType::Arrival => "Arrival".to_string(),
            NodeType::Transfer => "Transfer".to_string(),
        }
    }
}
