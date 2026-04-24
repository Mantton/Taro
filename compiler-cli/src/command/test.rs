use std::process::Command;

use compiler::error::ReportedError;

use crate::{TestArgs, command::build};

pub fn run(arguments: TestArgs) -> Result<(), ReportedError> {
    let exe = build::run_test_mode(arguments)?;
    let exe = exe.ok_or_else(|| {
        eprintln!("error: no test executable was produced");
        ReportedError
    })?;

    let status = Command::new(&exe).status().map_err(|e| {
        eprintln!("error: failed to execute '{}': {}", exe.display(), e);
        ReportedError
    })?;

    if status.success() {
        Ok(())
    } else {
        Err(ReportedError)
    }
}
