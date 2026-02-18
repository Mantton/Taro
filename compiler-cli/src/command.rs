use compiler::error::CompileResult;

use crate::CommandLineArguments;

mod build;
mod check;
mod new;
mod run;
mod test;

pub fn handle(arguments: CommandLineArguments) -> CompileResult<()> {
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
