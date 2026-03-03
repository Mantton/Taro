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

#[cfg(test)]
mod tests {
    use super::validate_test_selection_flags;
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
}
