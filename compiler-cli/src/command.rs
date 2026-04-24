use compiler::error::CompileResult;

use crate::{Cli, CliCommand};

mod build;
mod check;
mod incremental;
mod new;
mod run;
mod std_attached;
mod test;

pub fn handle(arguments: Cli) -> CompileResult<()> {
    let _ = match arguments.command {
        CliCommand::Build(arguments) => {
            build::run(arguments.common, false)?;
            ()
        }
        CliCommand::Check(arguments) => check::run(arguments)?,
        CliCommand::New(arguments) => new::run(arguments)?,
        CliCommand::Run(arguments) => run::run(arguments)?,
        CliCommand::Test(arguments) => test::run(arguments)?,
    };

    Ok(())
}

#[cfg(test)]
mod tests {
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
    fn rejects_program_args_for_new_command() {
        let args = Cli::try_parse_from(["taro", "new", "github.com/acme/app", "--", "foo"]);
        assert!(args.is_err());
    }

    #[test]
    fn rejects_program_args_for_test_command() {
        let args = Cli::try_parse_from(["taro", "test", "std", "--", "foo"]);
        assert!(args.is_err());
    }
}
