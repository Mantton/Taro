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

impl CommandLineArguments {
    /// Returns true if the path points to a single .tr file
    pub fn is_single_file(&self) -> bool {
        self.path.extension().map(|ext| ext == "tr").unwrap_or(false) && self.path.is_file()
    }
}

pub fn run() {
    let arguments = CommandLineArguments::parse();
    let result = command::handle(arguments);
    match result {
        Ok(_) => exit(0),
        Err(_) => exit(1),
    }
}
