use compiler::error::CompileResult;

use crate::CommandLineArguments;

mod build;
mod check;
mod run;

pub fn handle(arguments: CommandLineArguments) -> CompileResult<()> {
    let _ = match arguments.command.as_str() {
        "build" => {
            build::run(arguments, false)?;
            ()
        }
        "check" => check::run(arguments)?,
        "run" => run::run(arguments)?,
        _ => panic!("unknown command"),
    };

    Ok(())
}
