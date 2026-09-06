use clap::{Args, Parser, Subcommand, ValueEnum};
use compiler::compile::config::{
    BuildProfile, CodegenOptions, DebugInfo, LtoMode, ModuleArtifactKind, OptLevel,
    OptimizationMode,
};
use std::{path::PathBuf, process::exit, str::FromStr, time::Duration};

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
    Bench(BenchArgs),
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
    /// Select link-time optimization for participating Taro packages.
    #[arg(long = "lto", value_enum, default_value_t = Lto::Off)]
    pub lto: Lto,
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
    /// Select link-time optimization for participating Taro packages.
    #[arg(long = "lto", value_enum, default_value_t = Lto::Off)]
    pub lto: Lto,
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
pub struct BenchArgs {
    #[command(flatten)]
    pub common: CommonCompileArgs,
    /// List matching benchmark cases without running them.
    #[arg(long = "list")]
    pub list: bool,
    /// Case-insensitive substring filter against qualified benchmark names.
    #[arg(long = "filter")]
    pub filter: Option<String>,
    /// Case-insensitive benchmark tag filter. Repeat to match any requested tag.
    #[arg(long = "tag")]
    pub tag: Vec<String>,
    /// Warmup and calibration duration before measured samples.
    #[arg(long = "warmup", default_value = "250ms")]
    pub warmup: BenchDuration,
    /// Total target time divided across measured samples.
    #[arg(long = "time", default_value = "1s")]
    pub measurement_time: BenchDuration,
    /// Number of independent measured samples.
    #[arg(long = "samples", default_value_t = 20)]
    pub samples: usize,
    /// Maximum wall time for each isolated benchmark process.
    #[arg(long = "timeout", default_value = "30s")]
    pub timeout: BenchDuration,
    /// Select human-readable or stable machine-readable output.
    #[arg(long = "format", value_enum, default_value_t = BenchOutputFormat::Human)]
    pub format: BenchOutputFormat,
    /// Compile benchmarks with the debug profile instead of release/O2.
    #[arg(long = "debug", conflicts_with = "release")]
    pub debug: bool,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, ValueEnum)]
pub enum BenchOutputFormat {
    #[default]
    Human,
    Json,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct BenchDuration(u64);

impl BenchDuration {
    pub const fn as_nanos(self) -> u64 {
        self.0
    }

    pub const fn as_duration(self) -> Duration {
        Duration::from_nanos(self.0)
    }
}

impl FromStr for BenchDuration {
    type Err = String;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        let value = value.trim();
        let unit_start = value
            .char_indices()
            .find_map(|(index, character)| {
                (!character.is_ascii_digit() && character != '.').then_some(index)
            })
            .ok_or_else(|| "duration requires a unit: ns, us, ms, s, or m".to_string())?;
        let (number, unit) = value.split_at(unit_start);
        let number: f64 = number
            .parse()
            .map_err(|_| format!("invalid duration value {value:?}"))?;
        if !number.is_finite() || number < 0.0 {
            return Err(format!(
                "duration must be a finite non-negative value, got {value:?}"
            ));
        }
        let nanos_per_unit = match unit {
            "ns" => 1.0,
            "us" | "µs" | "μs" => 1_000.0,
            "ms" => 1_000_000.0,
            "s" => 1_000_000_000.0,
            "m" => 60_000_000_000.0,
            _ => {
                return Err(format!(
                    "unsupported duration unit {unit:?}; use ns, us, ms, s, or m"
                ));
            }
        };
        let nanos = number * nanos_per_unit;
        if nanos > u64::MAX as f64 {
            return Err(format!("duration {value:?} is too large"));
        }
        let rounded = nanos.round();
        if (nanos - rounded).abs() > 0.000_001 {
            return Err(format!(
                "duration {value:?} is more precise than one nanosecond"
            ));
        }
        Ok(Self(rounded as u64))
    }
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
    /// Build with the release profile (bench defaults to release; other commands default to debug).
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
    pub(crate) const fn module_artifact_kind(self, lto: Lto) -> ModuleArtifactKind {
        match (self, lto) {
            (Self::Link, Lto::Off) => ModuleArtifactKind::Object,
            (Self::Link, Lto::Full | Lto::Thin) | (Self::LlvmBitcode, _) => {
                ModuleArtifactKind::LlvmBitcode
            }
        }
    }
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, ValueEnum)]
pub enum Lto {
    #[default]
    Off,
    Full,
    Thin,
}

impl Lto {
    pub(crate) const fn is_enabled(self) -> bool {
        !matches!(self, Self::Off)
    }

    pub(crate) const fn mode(self) -> LtoMode {
        match self {
            Self::Off => LtoMode::Off,
            Self::Full => LtoMode::Full,
            Self::Thin => LtoMode::Thin,
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
                lto: LtoMode::Off,
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

impl BenchArgs {
    pub fn normalized_filter(&self) -> Option<String> {
        self.filter
            .as_ref()
            .map(|filter| filter.trim())
            .filter(|filter| !filter.is_empty())
            .map(ToOwned::to_owned)
    }

    pub fn normalized_tags(&self) -> Vec<String> {
        let mut normalized = Vec::new();
        for tag in &self.tag {
            let tag = tag.trim();
            if tag.is_empty()
                || normalized
                    .iter()
                    .any(|existing: &String| existing.eq_ignore_ascii_case(tag))
            {
                continue;
            }
            normalized.push(tag.to_owned());
        }
        normalized
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
    use super::{
        BenchDuration, BenchOutputFormat, BuildEmit, Cli, CliCommand, Lto, NewProjectKind,
    };
    use clap::Parser;
    use compiler::compile::config::{
        BuildProfile, DebugInfo, LtoMode, ModuleArtifactKind, OptLevel, OptimizationMode,
    };
    use std::str::FromStr;

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
            BuildEmit::LlvmBitcode.module_artifact_kind(Lto::Off),
            ModuleArtifactKind::LlvmBitcode
        );
    }

    #[test]
    fn build_and_run_parse_lto_modes_without_changing_the_default() {
        let build = Cli::parse_from(["taro", "build", "examples/hello.tr", "--lto", "full"]);
        let run = Cli::parse_from(["taro", "run", "examples/hello.tr", "--lto", "thin"]);
        let default = Cli::parse_from(["taro", "build", "examples/hello.tr"]);

        match build.command {
            CliCommand::Build(build) => {
                assert_eq!(build.lto, Lto::Full);
                assert_eq!(build.lto.mode(), LtoMode::Full);
                assert_eq!(
                    build.emit.module_artifact_kind(build.lto),
                    ModuleArtifactKind::LlvmBitcode
                );
            }
            other => panic!("expected build command, got {other:?}"),
        }
        match run.command {
            CliCommand::Run(run) => {
                assert_eq!(run.lto, Lto::Thin);
                assert_eq!(run.lto.mode(), LtoMode::Thin);
            }
            other => panic!("expected run command, got {other:?}"),
        }
        match default.command {
            CliCommand::Build(build) => assert_eq!(build.lto, Lto::Off),
            other => panic!("expected build command, got {other:?}"),
        }
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
    fn parses_benchmark_controls_and_defaults_to_human_output() {
        let args = Cli::parse_from([
            "taro",
            "bench",
            "std",
            "--filter",
            "json.parse",
            "--tag",
            "smoke",
            "--warmup",
            "1.5s",
            "--time",
            "2s",
            "--samples",
            "12",
            "--timeout",
            "1m",
        ]);
        let CliCommand::Bench(bench) = args.command else {
            panic!("expected bench command");
        };
        assert_eq!(bench.normalized_filter().as_deref(), Some("json.parse"));
        assert_eq!(bench.normalized_tags(), vec!["smoke"]);
        assert_eq!(bench.warmup.as_nanos(), 1_500_000_000);
        assert_eq!(bench.measurement_time.as_nanos(), 2_000_000_000);
        assert_eq!(bench.samples, 12);
        assert_eq!(bench.timeout.as_nanos(), 60_000_000_000);
        assert_eq!(bench.format, BenchOutputFormat::Human);
    }

    #[test]
    fn benchmark_duration_parser_rejects_missing_unknown_and_subnanosecond_units() {
        assert!(BenchDuration::from_str("10").is_err());
        assert!(BenchDuration::from_str("10fortnights").is_err());
        assert!(BenchDuration::from_str("0.1ns").is_err());
        assert_eq!(
            BenchDuration::from_str("250us").unwrap().as_nanos(),
            250_000
        );
    }

    #[test]
    fn benchmark_debug_and_release_flags_conflict() {
        assert!(Cli::try_parse_from(["taro", "bench", "std", "--debug", "--release"]).is_err());
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
        assert_eq!(debug.codegen.lto, LtoMode::Off);
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

#[cfg(test)]
#[path = "../../test_support.rs"]
mod test_support;
