use std::process::Command;

use compiler::error::ReportedError;

use crate::{
    TestArgs,
    command::{CommandOutcome, CommandResult, build, child_exit_code},
};

pub fn run(arguments: TestArgs) -> CommandResult {
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
        Ok(CommandOutcome::Success)
    } else {
        Ok(CommandOutcome::ChildExit(child_exit_code(status)))
    }
}
