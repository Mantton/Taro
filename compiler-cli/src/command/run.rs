use std::process::Command;

use compiler::error::ReportedError;

use crate::{CommandLineArguments, command::build};

pub fn run(arguments: CommandLineArguments) -> Result<(), ReportedError> {
    let exe = build::run(arguments, true)?;
    let exe = exe.ok_or(ReportedError)?;

    let status = Command::new(&exe).status().map_err(|_| ReportedError)?;
    if status.success() {
        Ok(())
    } else {
        Err(ReportedError)
    }
}
