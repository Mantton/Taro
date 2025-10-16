use crate::{ast, error::CompileResult};

mod tag;

pub fn resolve_package(package: &ast::Package) -> CompileResult<()> {
    // First Resolve DefinitionIDs
    tag::tag_package_symbols(package)?;
    Ok(())
}
