use std::process::Command;

use compiler::error::ReportedError;

use crate::{
    BuildEmit, RunArgs,
    command::{CommandOutcome, CommandResult, build, child_exit_code},
};

pub fn run(arguments: RunArgs) -> CommandResult {
    let program_args = arguments.program_args.clone();
    let runtime_stats = arguments.runtime_stats;
    let runtime_trace = arguments.runtime_trace;
    let exe = build::run(arguments.common, true, BuildEmit::Link)?;
    let exe = exe.ok_or_else(|| {
        eprintln!("error: no executable was produced");
        ReportedError
    })?;

    let mut command = Command::new(&exe);
    command.args(&program_args);
    if runtime_stats {
        command.env("TARO_RUNTIME_STATS", "1");
    }
    if runtime_trace {
        command.env("TARO_RUNTIME_TRACE", "1");
    }
    let status = command.status().map_err(|e| {
        eprintln!("error: failed to execute '{}': {}", exe.display(), e);
        ReportedError
    })?;

    if status.success() {
        Ok(CommandOutcome::Success)
    } else {
        Ok(CommandOutcome::ChildExit(child_exit_code(status)))
    }
}
