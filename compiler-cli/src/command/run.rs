use std::process::Command;

use compiler::error::ReportedError;

use crate::{RunArgs, command::build};

pub fn run(arguments: RunArgs) -> Result<(), ReportedError> {
    let program_args = arguments.program_args.clone();
    let exe = build::run(arguments.common, true)?;
    let exe = exe.ok_or_else(|| {
        eprintln!("error: no executable was produced");
        ReportedError
    })?;

    let status = Command::new(&exe)
        .args(&program_args)
        .status()
        .map_err(|e| {
            eprintln!("error: failed to execute '{}': {}", exe.display(), e);
            ReportedError
        })?;

    if status.success() {
        Ok(())
    } else {
        Err(ReportedError)
    }
}
