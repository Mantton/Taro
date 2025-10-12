use compiler::{compile, error::ReportedError};

use crate::CommandLineArguments;

pub fn run(arguments: CommandLineArguments) -> Result<(), ReportedError> {
    let project_path = arguments.path;
    compile::build(project_path)?;
    Ok(())
}
