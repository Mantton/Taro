use compiler::error::{CompileResult, ReportedError};

use crate::CommandLineArguments;

mod build;
mod check;
mod incremental;
mod new;
mod run;
mod std_attached;
mod test;

pub fn handle(arguments: CommandLineArguments) -> CompileResult<()> {
    validate_test_selection_flags(&arguments)?;
    validate_program_args(&arguments)?;

    let _ = match arguments.command.as_str() {
        "build" => {
            build::run(arguments, false)?;
            ()
        }
        "check" => check::run(arguments)?,
        "new" => new::run(arguments)?,
        "run" => run::run(arguments)?,
        "test" => test::run(arguments)?,
        _ => panic!("unknown command"),
    };

    Ok(())
}

fn validate_test_selection_flags(arguments: &CommandLineArguments) -> CompileResult<()> {
    if arguments.command == "test" {
        return Ok(());
    }

    let has_filter = arguments
        .filter
        .as_ref()
        .map(|s| !s.trim().is_empty())
        .unwrap_or(false);
    let has_tags = arguments.tag.iter().any(|s| !s.trim().is_empty());

    if has_filter || has_tags {
        eprintln!("error: --filter and --tag are only supported with the 'test' command");
        return Err(ReportedError);
    }

    Ok(())
}

fn validate_program_args(arguments: &CommandLineArguments) -> CompileResult<()> {
    if !arguments.has_program_args() {
        return Ok(());
    }

    if arguments.command == "run" {
        return Ok(());
    }

    eprintln!(
        "error: trailing program arguments after '--' are only supported with the 'run' command"
    );
    Err(ReportedError)
}

#[cfg(test)]
mod tests {
    use super::{validate_program_args, validate_test_selection_flags};
    use crate::CommandLineArguments;
    use clap::Parser;

    #[test]
    fn allows_filter_and_tag_for_test_command() {
        let args = CommandLineArguments::parse_from([
            "taro", "test", "std", "--filter", "core", "--tag", "smoke",
        ]);
        assert!(validate_test_selection_flags(&args).is_ok());
    }

    #[test]
    fn rejects_filter_for_non_test_command() {
        let args = CommandLineArguments::parse_from(["taro", "build", "std", "--filter", "core"]);
        assert!(validate_test_selection_flags(&args).is_err());
    }

    #[test]
    fn rejects_tag_for_non_test_command() {
        let args = CommandLineArguments::parse_from(["taro", "check", "std", "--tag", "smoke"]);
        assert!(validate_test_selection_flags(&args).is_err());
    }

    #[test]
    fn allows_program_args_for_run_command() {
        let args = CommandLineArguments::parse_from(["taro", "run", "std", "--", "foo", "bar"]);
        assert!(validate_program_args(&args).is_ok());
    }

    #[test]
    fn rejects_program_args_for_build_command() {
        let args = CommandLineArguments::parse_from(["taro", "build", "std", "--", "foo"]);
        assert!(validate_program_args(&args).is_err());
    }

    #[test]
    fn rejects_program_args_for_check_command() {
        let args = CommandLineArguments::parse_from(["taro", "check", "std", "--", "foo"]);
        assert!(validate_program_args(&args).is_err());
    }

    #[test]
    fn rejects_program_args_for_new_command() {
        let args = CommandLineArguments::parse_from(["taro", "new", "std", "--", "foo"]);
        assert!(validate_program_args(&args).is_err());
    }

    #[test]
    fn rejects_program_args_for_test_command() {
        let args = CommandLineArguments::parse_from(["taro", "test", "std", "--", "foo"]);
        assert!(validate_program_args(&args).is_err());
    }
}
