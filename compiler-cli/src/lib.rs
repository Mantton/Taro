use clap::Parser;
use std::path::PathBuf;

mod command;

#[derive(Parser, Clone, Debug)]
pub struct CommandLineArguments {
    pub command: String,
    pub path: PathBuf,
}

pub fn run() {
    let arguments = CommandLineArguments::parse();
    command::handle(arguments);
}
