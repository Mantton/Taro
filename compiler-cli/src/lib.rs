use clap::Parser;
use std::{path::PathBuf, process::exit};

mod command;
mod package;

#[derive(Parser, Clone, Debug)]
pub struct CommandLineArguments {
    pub command: String,
    pub path: PathBuf,
    #[arg(short = 'o', long = "output")]
    pub output: Option<PathBuf>,
    #[arg(long = "std-path")]
    pub std_path: Option<PathBuf>,
}

pub fn run() {
    let arguments = CommandLineArguments::parse();
    let result = command::handle(arguments);

    match result {
        Ok(_) => {
            println!("compilation successful");
            exit(0)
        }
        Err(_) => {
            println!("compilation failed");
            exit(1)
        }
    }
}
