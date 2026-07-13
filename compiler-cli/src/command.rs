use std::process::ExitStatus;

use compiler::error::ReportedError;

use crate::{Cli, CliCommand};

mod build;
mod check;
mod compile_paths;
mod incremental;
mod new;
mod run;
mod runtime_artifact;
mod std_attached;
mod test;

pub type CommandResult = Result<CommandOutcome, ReportedError>;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CommandOutcome {
    Success,
    ChildExit(i32),
}

impl CommandOutcome {
    pub fn process_exit_code(self) -> i32 {
        match self {
            CommandOutcome::Success => 0,
            CommandOutcome::ChildExit(code) => code,
        }
    }
}

pub(crate) fn child_exit_code(status: ExitStatus) -> i32 {
    if let Some(code) = status.code() {
        return code;
    }

    signal_exit_code(&status).unwrap_or(1)
}

#[cfg(unix)]
fn signal_exit_code(status: &ExitStatus) -> Option<i32> {
    use std::os::unix::process::ExitStatusExt;

    status.signal().map(|signal| 128 + signal)
}

#[cfg(not(unix))]
fn signal_exit_code(_status: &ExitStatus) -> Option<i32> {
    None
}

pub fn handle(arguments: Cli) -> CommandResult {
    match arguments.command {
        CliCommand::Build(arguments) => {
            build::run(arguments.common, false, arguments.emit)?;
            ()
        }
        CliCommand::Check(arguments) => check::run(arguments)?,
        CliCommand::New(arguments) => new::run(arguments)?,
        CliCommand::Run(arguments) => return run::run(arguments),
        CliCommand::RuntimeManifest(arguments) => {
            match runtime_artifact::write_manifest(&arguments.archive, arguments.target.as_deref())
            {
                Ok(path) => eprintln!("Generated runtime manifest – {}", path.display()),
                Err(error) => {
                    eprintln!("error: {error}");
                    return Err(ReportedError);
                }
            }
        }
        CliCommand::Test(arguments) => return test::run(arguments),
    }

    Ok(CommandOutcome::Success)
}

#[cfg(test)]
mod tests {
    use super::{CommandOutcome, child_exit_code};
    use crate::Cli;
    use clap::Parser;

    #[test]
    fn rejects_filter_for_build_command() {
        let args = Cli::try_parse_from(["taro", "build", "std", "--filter", "core"]);
        assert!(args.is_err());
    }

    #[test]
    fn rejects_tag_for_check_command() {
        let args = Cli::try_parse_from(["taro", "check", "std", "--tag", "smoke"]);
        assert!(args.is_err());
    }

    #[test]
    fn allows_program_args_for_run_command() {
        let args = Cli::try_parse_from(["taro", "run", "std", "--", "foo", "bar"]);
        assert!(args.is_ok());
    }

    #[test]
    fn rejects_program_args_for_build_command() {
        let args = Cli::try_parse_from(["taro", "build", "std", "--", "foo"]);
        assert!(args.is_err());
    }

    #[test]
    fn rejects_build_emit_mode_for_run_command() {
        let args = Cli::try_parse_from(["taro", "run", "main.tr", "--emit", "llvm-bc"]);
        assert!(args.is_err());
    }

    #[test]
    fn rejects_program_args_for_new_command() {
        let args = Cli::try_parse_from(["taro", "new", "github.com/acme/app", "--", "foo"]);
        assert!(args.is_err());
    }

    #[test]
    fn rejects_program_args_for_test_command() {
        let args = Cli::try_parse_from(["taro", "test", "std", "--", "foo"]);
        assert!(args.is_err());
    }

    #[test]
    fn success_outcome_exits_zero() {
        assert_eq!(CommandOutcome::Success.process_exit_code(), 0);
    }

    #[test]
    fn child_outcome_preserves_exit_code() {
        assert_eq!(CommandOutcome::ChildExit(42).process_exit_code(), 42);
    }

    #[cfg(unix)]
    #[test]
    fn child_exit_code_preserves_unix_status_code() {
        use std::{os::unix::process::ExitStatusExt, process::ExitStatus};

        let status = ExitStatus::from_raw(42 << 8);

        assert_eq!(child_exit_code(status), 42);
    }

    #[cfg(unix)]
    #[test]
    fn child_exit_code_maps_unix_signal_status() {
        use std::{os::unix::process::ExitStatusExt, process::ExitStatus};

        let status = ExitStatus::from_raw(9);

        assert_eq!(child_exit_code(status), 137);
    }

    #[cfg(windows)]
    #[test]
    fn child_exit_code_preserves_windows_status_code() {
        use std::{os::windows::process::ExitStatusExt, process::ExitStatus};

        let status = ExitStatus::from_raw(42);

        assert_eq!(child_exit_code(status), 42);
    }
}
