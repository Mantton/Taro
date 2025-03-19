use super::Declaration;
use super::NodeID;
use taroc_span::{FileID, Symbol};

#[derive(Debug)]
pub struct Package {
    pub root: Module,
}

#[derive(Debug)]
pub struct Module {
    pub id: NodeID,
    pub name: Symbol,
    pub files: Vec<File>,
    pub submodules: Vec<Module>,
}

#[derive(Debug)]
pub struct File {
    pub declarations: Vec<Declaration>,
    pub id: FileID,
}
