index_vec::define_index_type! {
    pub struct NodeID = u32;
}

pub struct NodeTagger {
    next_index: u32,
}

impl NodeTagger {
    pub fn new() -> Self {
        NodeTagger { next_index: 1 }
    }

    pub fn next(&mut self) -> NodeID {
        let id = NodeID::from_raw(self.next_index);
        self.next_index += 1;
        id
    }
}
