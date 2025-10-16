use compiler::error::CompileResult;

use crate::CommandLineArguments;

mod build;

pub fn handle(arguments: CommandLineArguments) -> CompileResult<()> {
    let _ = match arguments.command.as_str() {
        "build" => build::run(arguments)?,
        _ => panic!("unknown command"),
    };

    Ok(())
}
