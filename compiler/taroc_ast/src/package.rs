use taroc_span::{FileID, Symbol};

use super::Declaration;

#[derive(Debug)]
pub struct Package {
    pub root: Module,
}

#[derive(Debug)]
pub struct Module {
    pub name: Symbol,
    pub files: Vec<File>,
    pub submodules: Vec<Module>,
}

#[derive(Debug)]
pub struct File {
    pub declarations: Vec<Declaration>,
    pub file: FileID,
}
