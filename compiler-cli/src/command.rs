use crate::CommandLineArguments;

mod build;

pub fn handle(arguments: CommandLineArguments) {
    let _ = match arguments.command.as_str() {
        "build" => build::run(arguments),
        _ => panic!("unknown command"),
    };
}
