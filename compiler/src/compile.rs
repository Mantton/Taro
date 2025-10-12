use crate::{
    diagnostics::DiagCtx,
    error::ReportedError,
    parse::{self},
};
use std::path::PathBuf;

pub fn build(project_path: PathBuf) -> Result<(), ReportedError> {
    let dcx = DiagCtx::new();
    let package = parse::lexer::tokenize_package(project_path, &dcx)?;
    let _ = parse::parser::parse_package(package, &dcx)?;
    Ok(())
}
