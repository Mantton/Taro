use clap::{Args, Parser, Subcommand, ValueEnum};
use compiler::compile::config::{
    BuildProfile, CodegenOptions, DebugInfo, ModuleArtifactKind, OptLevel, OptimizationMode,
};
use std::{path::PathBuf, process::exit};

mod command;
mod package;

#[derive(Clone, Copy, Debug)]
pub struct CompileModeOptions {
    pub profile: BuildProfile,
    pub codegen: CodegenOptions,
    pub overflow_checks: bool,
    pub timings: bool,
    pub debug_info: DebugInfo,
}

#[derive(Parser, Clone, Debug)]
#[command(name = "taro", bin_name = "taro")]
pub struct Cli {
    /// Print LLVM passed, missed, and analysis remarks matching a pass-name regex.
    #[arg(
        long = "optimization-remarks",
        global = true,
        value_name = "PASS_REGEX"
    )]
    pub optimization_remarks: Option<String>,
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
    #[command(hide = true)]
    RuntimeManifest(RuntimeManifestArgs),
}

#[derive(Args, Clone, Debug)]
pub struct BuildArgs {
    #[command(flatten)]
    pub common: CommonCompileArgs,
    /// Select the final build artifact.
    #[arg(long = "emit", value_enum, default_value_t = BuildEmit::Link)]
    pub emit: BuildEmit,
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
    /// Print a scheduler, I/O, and GC summary when the program exits.
    #[arg(long = "runtime-stats")]
    pub runtime_stats: bool,
    /// Print a bounded scheduler, I/O, and GC event trace when the program exits.
    #[arg(long = "runtime-trace")]
    pub runtime_trace: bool,
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
pub struct RuntimeManifestArgs {
    /// Static runtime archive to inspect and describe.
    pub archive: PathBuf,
    /// Target triple the archive was built for. Omit for a host-only archive.
    #[arg(long = "target")]
    pub target: Option<String>,
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
    /// Source debug metadata to emit (defaults to line tables in debug builds).
    #[arg(long = "debug-info", value_enum)]
    pub debug_info: Option<DebugInfoLevel>,
    #[arg(long = "runtime-path")]
    pub runtime_path: Option<PathBuf>,
    /// Target triple override (e.g., x86_64-unknown-linux-gnu)
    #[arg(long = "target")]
    pub target: Option<String>,
    /// Clang-compatible linker driver used for the selected target.
    #[arg(long = "linker")]
    pub linker: Option<PathBuf>,
    /// Target SDK/sysroot passed to the linker driver.
    #[arg(long = "sysroot")]
    pub sysroot: Option<PathBuf>,
    /// Build with release profile (default is debug).
    #[arg(long = "release")]
    pub release: bool,
    /// Select the LLVM optimization level independently of the build profile.
    #[arg(short = 'O', value_enum, value_name = "LEVEL")]
    pub opt_level: Option<OptimizationLevelArg>,
    /// Force integer overflow checks on.
    #[arg(long = "overflow-checks", conflicts_with = "no_overflow_checks")]
    pub overflow_checks: bool,
    /// Force integer overflow checks off.
    #[arg(long = "no-overflow-checks", conflicts_with = "overflow_checks")]
    pub no_overflow_checks: bool,
    /// Print compiler phase timings through artifact emission and optional linking.
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
    Both,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, ValueEnum)]
pub enum BuildEmit {
    /// Produce the package's normal linked executable when applicable.
    #[default]
    Link,
    /// Produce optimized LLVM bitcode without native code generation or linking.
    #[value(name = "llvm-bc")]
    LlvmBitcode,
}

impl BuildEmit {
    pub(crate) const fn module_artifact_kind(self) -> ModuleArtifactKind {
        match self {
            Self::Link => ModuleArtifactKind::Object,
            Self::LlvmBitcode => ModuleArtifactKind::LlvmBitcode,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, ValueEnum)]
pub enum DebugInfoLevel {
    None,
    LineTables,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, ValueEnum)]
pub enum OptimizationLevelArg {
    /// Pre-O2-rollout pipeline retained for compiler regression comparisons.
    #[value(name = "baseline", hide = true)]
    Baseline,
    #[value(name = "0")]
    O0,
    #[value(name = "1")]
    O1,
    #[value(name = "2")]
    O2,
    #[value(name = "3")]
    O3,
    #[value(name = "s")]
    Os,
    #[value(name = "z")]
    Oz,
}

impl OptimizationLevelArg {
    fn optimization_mode(self) -> OptimizationMode {
        match self {
            OptimizationLevelArg::Baseline => OptimizationMode::Baseline,
            OptimizationLevelArg::O0 => OptimizationMode::Level(OptLevel::O0),
            OptimizationLevelArg::O1 => OptimizationMode::Level(OptLevel::O1),
            OptimizationLevelArg::O2 => OptimizationMode::Level(OptLevel::O2),
            OptimizationLevelArg::O3 => OptimizationMode::Level(OptLevel::O3),
            OptimizationLevelArg::Os => OptimizationMode::Level(OptLevel::Os),
            OptimizationLevelArg::Oz => OptimizationMode::Level(OptLevel::Oz),
        }
    }
}

impl From<DebugInfoLevel> for DebugInfo {
    fn from(value: DebugInfoLevel) -> Self {
        match value {
            DebugInfoLevel::None => DebugInfo::None,
            DebugInfoLevel::LineTables => DebugInfo::LineTables,
        }
    }
}

fn default_optimization_mode(profile: BuildProfile) -> OptimizationMode {
    match profile {
        BuildProfile::Debug => OptimizationMode::Baseline,
        BuildProfile::Release => OptimizationMode::Level(OptLevel::O2),
    }
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
        let profile = self.build_profile();
        let optimization = self
            .opt_level
            .map(OptimizationLevelArg::optimization_mode)
            .unwrap_or_else(|| default_optimization_mode(profile));
        CompileModeOptions {
            profile,
            codegen: CodegenOptions {
                optimization,
                artifact: ModuleArtifactKind::Object,
            },
            overflow_checks: self.overflow_checks_enabled(),
            timings: self.timings,
            debug_info: self.debug_info.map(Into::into).unwrap_or_else(|| {
                if matches!(profile, BuildProfile::Debug) {
                    DebugInfo::LineTables
                } else {
                    DebugInfo::None
                }
            }),
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
    if let Some(pass_filter) = arguments.optimization_remarks.as_deref()
        && let Err(error) = compiler::codegen::configure_optimization_remarks(pass_filter)
    {
        eprintln!("error: {error}");
        exit(2);
    }
    let result = command::handle(arguments);
    let exit_code = match result {
        Ok(outcome) => outcome.process_exit_code(),
        Err(_) => 1,
    };
    exit(exit_code)
}

#[cfg(test)]
mod tests {
    use super::{BuildEmit, Cli, CliCommand, NewProjectKind};
    use clap::Parser;
    use compiler::compile::config::{
        BuildProfile, DebugInfo, ModuleArtifactKind, OptLevel, OptimizationMode,
    };

    #[test]
    fn build_defaults_to_link_and_parses_llvm_bitcode_output() {
        let linked = Cli::parse_from(["taro", "build", "examples/hello.tr"]);
        let bitcode = Cli::parse_from(["taro", "build", "examples/hello.tr", "--emit", "llvm-bc"]);

        let emit = |cli: Cli| match cli.command {
            CliCommand::Build(build) => build.emit,
            other => panic!("expected build command, got {other:?}"),
        };
        assert_eq!(emit(linked), BuildEmit::Link);
        assert_eq!(emit(bitcode), BuildEmit::LlvmBitcode);
        assert_eq!(
            BuildEmit::LlvmBitcode.module_artifact_kind(),
            ModuleArtifactKind::LlvmBitcode
        );
    }

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
    fn parses_new_command_with_both_kind() {
        let args = Cli::parse_from(["taro", "new", "github.com/acme/app", "--kind", "both"]);

        match args.command {
            CliCommand::New(new) => assert_eq!(new.kind, NewProjectKind::Both),
            other => panic!("expected new command, got {other:?}"),
        }
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
    fn parses_runtime_diagnostic_flags_for_run() {
        let run = Cli::parse_from([
            "taro",
            "run",
            "main.tr",
            "--runtime-stats",
            "--runtime-trace",
        ]);
        match run.command {
            CliCommand::Run(run) => {
                assert!(run.runtime_stats);
                assert!(run.runtime_trace);
            }
            other => panic!("expected run command, got {other:?}"),
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
    fn parses_target_linker_and_sysroot() {
        let args = Cli::parse_from([
            "taro",
            "build",
            "std",
            "--target",
            "aarch64-unknown-linux-gnu",
            "--linker",
            "/opt/cross/bin/clang",
            "--sysroot",
            "/opt/cross/sysroot",
        ]);

        match args.command {
            CliCommand::Build(build) => {
                assert_eq!(
                    build.common.target.as_deref(),
                    Some("aarch64-unknown-linux-gnu")
                );
                assert_eq!(
                    build.common.linker.as_deref(),
                    Some(std::path::Path::new("/opt/cross/bin/clang"))
                );
                assert_eq!(
                    build.common.sysroot.as_deref(),
                    Some(std::path::Path::new("/opt/cross/sysroot"))
                );
            }
            other => panic!("expected build command, got {other:?}"),
        }
    }

    #[test]
    fn parses_internal_runtime_manifest_command() {
        let args = Cli::parse_from([
            "taro",
            "runtime-manifest",
            "libtaro_runtime.a",
            "--target",
            "aarch64-unknown-linux-gnu",
        ]);

        match args.command {
            CliCommand::RuntimeManifest(manifest) => {
                assert_eq!(manifest.archive, std::path::Path::new("libtaro_runtime.a"));
                assert_eq!(
                    manifest.target.as_deref(),
                    Some("aarch64-unknown-linux-gnu")
                );
            }
            other => panic!("expected runtime-manifest command, got {other:?}"),
        }
    }

    #[test]
    fn selects_debug_info_from_profile_and_override() {
        let debug = Cli::parse_from(["taro", "build", "examples/hello.tr"]);
        let release = Cli::parse_from(["taro", "build", "examples/hello.tr", "--release"]);
        let overridden = Cli::parse_from([
            "taro",
            "build",
            "examples/hello.tr",
            "--release",
            "--debug-info",
            "line-tables",
        ]);

        let mode = |cli: Cli| match cli.command {
            CliCommand::Build(build) => build.common.compile_mode_options().debug_info,
            other => panic!("expected build command, got {other:?}"),
        };
        assert_eq!(mode(debug), DebugInfo::LineTables);
        assert_eq!(mode(release), DebugInfo::None);
        assert_eq!(mode(overridden), DebugInfo::LineTables);
    }

    #[test]
    fn selects_profile_optimization_defaults_and_explicit_overrides() {
        let debug = Cli::parse_from(["taro", "build", "examples/hello.tr"]);
        let release = Cli::parse_from(["taro", "build", "examples/hello.tr", "--release"]);
        let optimized = Cli::parse_from(["taro", "build", "examples/hello.tr", "-O2"]);
        let size_optimized =
            Cli::parse_from(["taro", "build", "examples/hello.tr", "--release", "-Oz"]);
        let retained_baseline = Cli::parse_from([
            "taro",
            "build",
            "examples/hello.tr",
            "--release",
            "-Obaseline",
        ]);

        let mode = |cli: Cli| match cli.command {
            CliCommand::Build(build) => build.common.compile_mode_options(),
            other => panic!("expected build command, got {other:?}"),
        };
        let debug = mode(debug);
        let release = mode(release);
        let optimized = mode(optimized);
        let size_optimized = mode(size_optimized);
        let retained_baseline = mode(retained_baseline);
        assert_eq!(debug.codegen.optimization, OptimizationMode::Baseline);
        assert_eq!(debug.codegen.artifact, ModuleArtifactKind::Object);
        assert_eq!(
            release.codegen.optimization,
            OptimizationMode::Level(OptLevel::O2)
        );
        assert_eq!(
            optimized.codegen.optimization,
            OptimizationMode::Level(OptLevel::O2)
        );
        assert_eq!(
            size_optimized.codegen.optimization,
            OptimizationMode::Level(OptLevel::Oz)
        );
        assert_eq!(optimized.profile, BuildProfile::Debug);
        assert_eq!(size_optimized.profile, BuildProfile::Release);
        assert_eq!(retained_baseline.profile, BuildProfile::Release);
        assert_eq!(
            retained_baseline.codegen.optimization,
            OptimizationMode::Baseline
        );
    }

    #[test]
    fn parses_global_optimization_remark_filter() {
        let arguments = Cli::parse_from([
            "taro",
            "build",
            "examples/hello.tr",
            "--optimization-remarks",
            "inline|loop-vectorize",
        ]);

        assert_eq!(
            arguments.optimization_remarks.as_deref(),
            Some("inline|loop-vectorize")
        );
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
