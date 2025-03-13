use std::process::exit;

use taroc_error::CompileError;

use crate::arguments::CommandLineArguments;
mod build;

pub fn handle(arguments: CommandLineArguments) {
    let result = match arguments.command.as_str() {
        "build" => build::run(arguments),
        _ => panic!("unknown command"),
    };

    match result {
        Ok(_) => exit(0),
        Err(CompileError::Reported) => exit(1),
        Err(CompileError::Message(message)) => {
            eprintln!("error: {}", message);
            exit(1)
        }
    }
}
