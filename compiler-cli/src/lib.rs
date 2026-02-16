use clap::Parser;
use compiler::compile::config::BuildProfile;
use std::{path::PathBuf, process::exit};

mod command;
mod package;

#[derive(Clone, Copy, Debug)]
pub struct CompileModeOptions {
    pub profile: BuildProfile,
    pub overflow_checks: bool,
}

#[derive(Parser, Clone, Debug)]
pub struct CommandLineArguments {
    pub command: String,
    pub path: PathBuf,
    #[arg(short = 'o', long = "output")]
    pub output: Option<PathBuf>,
    #[arg(long = "std-path")]
    pub std_path: Option<PathBuf>,
    /// Dump MIR for all functions to stderr
    #[arg(long = "dump-mir")]
    pub dump_mir: bool,
    /// Dump generated LLVM IR to stderr
    #[arg(long = "dump-llvm")]
    pub dump_llvm: bool,
    #[arg(long = "runtime-path")]
    pub runtime_path: Option<PathBuf>,
    /// Target triple override (e.g., x86_64-unknown-linux-gnu)
    #[arg(long = "target")]
    pub target: Option<String>,
    /// Build with release profile (default is debug).
    #[arg(long = "release")]
    pub release: bool,
    /// Force integer overflow checks on.
    #[arg(long = "overflow-checks", conflicts_with = "no_overflow_checks")]
    pub overflow_checks: bool,
    /// Force integer overflow checks off.
    #[arg(long = "no-overflow-checks", conflicts_with = "overflow_checks")]
    pub no_overflow_checks: bool,
}

impl CommandLineArguments {
    /// Returns true if the path points to a single .tr file
    pub fn is_single_file(&self) -> bool {
        self.path
            .extension()
            .map(|ext| ext == "tr")
            .unwrap_or(false)
            && self.path.is_file()
    }

    pub fn build_profile(&self) -> BuildProfile {
        if self.release {
            BuildProfile::Release
        } else {
            BuildProfile::Debug
        }
    }

    pub fn overflow_checks_enabled(&self) -> bool {
        if self.overflow_checks {
            true
        } else if self.no_overflow_checks {
            false
        } else {
            matches!(self.build_profile(), BuildProfile::Debug)
        }
    }

    pub fn compile_mode_options(&self) -> CompileModeOptions {
        CompileModeOptions {
            profile: self.build_profile(),
            overflow_checks: self.overflow_checks_enabled(),
        }
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
