use clap::Parser;
use compiler::compile::config::BuildProfile;
use std::{path::PathBuf, process::exit};

mod command;
mod package;

#[derive(Clone, Copy, Debug)]
pub struct CompileModeOptions {
    pub profile: BuildProfile,
    pub overflow_checks: bool,
    pub timings: bool,
}

#[derive(Parser, Clone, Debug)]
pub struct CommandLineArguments {
    pub command: String,
    pub path: PathBuf,
    /// Case-insensitive substring filter against qualified test names.
    #[arg(long = "filter")]
    pub filter: Option<String>,
    /// Case-insensitive test tag filter. Repeat to match any requested tag.
    #[arg(long = "tag")]
    pub tag: Vec<String>,
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
    /// Print compiler phase timings (parse -> link) to stderr.
    #[arg(long = "timings")]
    pub timings: bool,
    /// Disable incremental dependency reuse and force cold compilation.
    #[arg(long = "no-incremental")]
    pub no_incremental: bool,
    /// Rebuild and publish attached std artifacts from source.
    #[arg(long = "build-std")]
    pub build_std: bool,
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
            timings: self.timings,
        }
    }

    pub fn normalized_test_filter(&self) -> Option<String> {
        self.filter
            .as_ref()
            .map(|s| s.trim())
            .filter(|s| !s.is_empty())
            .map(ToOwned::to_owned)
    }

    pub fn normalized_test_tags(&self) -> Vec<String> {
        self.tag
            .iter()
            .map(|s| s.trim())
            .filter(|s| !s.is_empty())
            .map(ToOwned::to_owned)
            .collect()
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

#[cfg(test)]
mod tests {
    use super::CommandLineArguments;
    use clap::Parser;

    #[test]
    fn parses_test_filter_and_tags() {
        let args = CommandLineArguments::parse_from([
            "taro",
            "test",
            "std",
            "--filter",
            "Core.Tests",
            "--tag",
            "Smoke",
            "--tag",
            "slow",
        ]);

        assert_eq!(args.command, "test");
        assert_eq!(args.normalized_test_filter().as_deref(), Some("Core.Tests"));
        assert_eq!(args.normalized_test_tags(), vec!["Smoke", "slow"]);
    }

    #[test]
    fn normalized_filter_and_tags_trim_and_drop_empty() {
        let args = CommandLineArguments::parse_from([
            "taro",
            "test",
            "std",
            "--filter",
            "  core.tests  ",
            "--tag",
            " Smoke ",
            "--tag",
            "   ",
        ]);

        assert_eq!(args.normalized_test_filter().as_deref(), Some("core.tests"));
        assert_eq!(args.normalized_test_tags(), vec!["Smoke"]);
    }
}
