use clap::{Args, Parser, Subcommand, ValueEnum};
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
#[command(name = "taro", bin_name = "taro")]
pub struct Cli {
    #[command(subcommand)]
    pub command: CliCommand,
}

#[derive(Subcommand, Clone, Debug)]
pub enum CliCommand {
    Build(BuildArgs),
    Check(CheckArgs),
    Run(RunArgs),
    Test(TestArgs),
    New(NewArgs),
}

#[derive(Args, Clone, Debug)]
pub struct BuildArgs {
    #[command(flatten)]
    pub common: CommonCompileArgs,
}

#[derive(Args, Clone, Debug)]
pub struct CheckArgs {
    #[command(flatten)]
    pub common: CommonCompileArgs,
}

#[derive(Args, Clone, Debug)]
pub struct RunArgs {
    #[command(flatten)]
    pub common: CommonCompileArgs,
    /// Program arguments forwarded to the compiled executable after `--`.
    #[arg(last = true)]
    pub program_args: Vec<String>,
}

#[derive(Args, Clone, Debug)]
pub struct TestArgs {
    #[command(flatten)]
    pub common: CommonCompileArgs,
    /// Case-insensitive substring filter against qualified test names.
    #[arg(long = "filter")]
    pub filter: Option<String>,
    /// Case-insensitive test tag filter. Repeat to match any requested tag.
    #[arg(long = "tag")]
    pub tag: Vec<String>,
}

#[derive(Args, Clone, Debug)]
pub struct NewArgs {
    pub package: String,
    #[arg(long = "kind", value_enum, default_value_t = NewProjectKind::Executable)]
    pub kind: NewProjectKind,
}

#[derive(Args, Clone, Debug)]
pub struct CommonCompileArgs {
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
    /// Print compiler phase timings (parse -> link) to stderr.
    #[arg(long = "timings")]
    pub timings: bool,
    /// Disable incremental dependency reuse and force cold compilation.
    #[arg(long = "no-incremental")]
    pub no_incremental: bool,
    /// Rebuild and publish attached std artifacts from source.
    #[arg(long = "build-std")]
    pub build_std: bool,
    /// Require dependency resolution to match package.lock exactly.
    #[arg(long = "locked")]
    pub locked: bool,
    /// Refresh package.lock entries from current dependency sources.
    #[arg(long = "update-lock", conflicts_with = "locked")]
    pub update_lock: bool,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, ValueEnum)]
pub enum NewProjectKind {
    #[default]
    Executable,
    Library,
}

impl CommonCompileArgs {
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

    pub fn sync_options(&self) -> crate::package::sync::SyncOptions {
        crate::package::sync::SyncOptions {
            locked: self.locked,
            update_lock: self.update_lock,
            strict_env: ci_env_is_strict(),
        }
    }
}

impl TestArgs {
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

fn ci_env_is_strict() -> bool {
    let Ok(value) = std::env::var("CI") else {
        return false;
    };

    let normalized = value.trim().to_ascii_lowercase();
    !(normalized.is_empty() || normalized == "0" || normalized == "false" || normalized == "no")
}

pub fn run() {
    let arguments = Cli::parse();
    let result = command::handle(arguments);
    match result {
        Ok(_) => exit(0),
        Err(_) => exit(1),
    }
}

#[cfg(test)]
mod tests {
    use super::{Cli, CliCommand, NewProjectKind};
    use clap::Parser;

    #[test]
    fn parses_new_command() {
        let args = Cli::parse_from(["taro", "new", "github.com/acme/app"]);

        match args.command {
            CliCommand::New(new) => {
                assert_eq!(new.package, "github.com/acme/app");
                assert_eq!(new.kind, NewProjectKind::Executable);
            }
            other => panic!("expected new command, got {other:?}"),
        }
    }

    #[test]
    fn parses_new_command_with_library_kind() {
        let args = Cli::parse_from(["taro", "new", "github.com/acme/app", "--kind", "library"]);

        match args.command {
            CliCommand::New(new) => assert_eq!(new.kind, NewProjectKind::Library),
            other => panic!("expected new command, got {other:?}"),
        }
    }

    #[test]
    fn rejects_new_command_with_unsupported_kind() {
        let args = Cli::try_parse_from(["taro", "new", "github.com/acme/app", "--kind", "both"]);
        assert!(args.is_err());
    }

    #[test]
    fn parses_test_filter_and_tags() {
        let args = Cli::parse_from([
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

        match args.command {
            CliCommand::Test(test) => {
                assert_eq!(test.normalized_test_filter().as_deref(), Some("Core.Tests"));
                assert_eq!(test.normalized_test_tags(), vec!["Smoke", "slow"]);
            }
            other => panic!("expected test command, got {other:?}"),
        }
    }

    #[test]
    fn normalized_filter_and_tags_trim_and_drop_empty() {
        let args = Cli::parse_from([
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

        match args.command {
            CliCommand::Test(test) => {
                assert_eq!(test.normalized_test_filter().as_deref(), Some("core.tests"));
                assert_eq!(test.normalized_test_tags(), vec!["Smoke"]);
            }
            other => panic!("expected test command, got {other:?}"),
        }
    }

    #[test]
    fn parses_lock_flags() {
        let args = Cli::parse_from(["taro", "build", "std", "--locked"]);

        match args.command {
            CliCommand::Build(build) => {
                assert!(build.common.locked);
                assert!(!build.common.update_lock);
            }
            other => panic!("expected build command, got {other:?}"),
        }
    }

    #[test]
    fn parses_run_program_args_after_double_dash() {
        let args = Cli::parse_from(["taro", "run", "examples/hello.tr", "--", "foo", "bar"]);

        match args.command {
            CliCommand::Run(run) => assert_eq!(run.program_args, vec!["foo", "bar"]),
            other => panic!("expected run command, got {other:?}"),
        }
    }

    #[test]
    fn parses_empty_program_args_when_double_dash_is_last() {
        let args = Cli::parse_from(["taro", "run", "examples/hello.tr", "--"]);

        match args.command {
            CliCommand::Run(run) => assert!(run.program_args.is_empty()),
            other => panic!("expected run command, got {other:?}"),
        }
    }

    #[test]
    fn parses_without_program_args() {
        let args = Cli::parse_from(["taro", "run", "examples/hello.tr"]);

        match args.command {
            CliCommand::Run(run) => assert!(run.program_args.is_empty()),
            other => panic!("expected run command, got {other:?}"),
        }
    }
}
