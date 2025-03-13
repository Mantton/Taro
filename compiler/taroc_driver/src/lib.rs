mod arguments;
mod command;

use arguments::CommandLineArguments;
use clap::Parser;

pub fn run() {
    let arguments = CommandLineArguments::parse();
    command::handle(arguments);
}
