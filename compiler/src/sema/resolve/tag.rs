use crate::{
    ast::{self, AstVisitor, walk_package},
    error::CompileResult,
};

pub fn tag_package_symbols(package: &ast::Package) -> CompileResult<()> {
    let mut actor = Actor {};
    walk_package(&mut actor, package);
    Ok(())
}

struct Actor {}

impl AstVisitor for Actor {}

impl Actor {}
