use compiler::{compile, error::ReportedError};

use crate::{CommandLineArguments, package::sync::sync_dependencies};

pub fn run(arguments: CommandLineArguments) -> Result<(), ReportedError> {
    let project_path = arguments.path;
    let _ = sync_dependencies(project_path.clone())?;
    compile::build(project_path)?;
    Ok(())
}
