use compiler::error::CompileResult;

use crate::CommandLineArguments;

mod build;
mod run;

pub fn handle(arguments: CommandLineArguments) -> CompileResult<()> {
    let _ = match arguments.command.as_str() {
        "build" => {
            build::run(arguments, false)?;
            ()
        }
        "run" => run::run(arguments)?,
        _ => panic!("unknown command"),
    };

    Ok(())
}
