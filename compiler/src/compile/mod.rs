use crate::{
    ast_lowering, cfg_eval, codegen,
    codegen::artifact::ModuleArtifact,
    compile::{
        config::{Config, ModuleArtifactKind},
        context::{CompilerContext, GlobalContext},
    },
    error::CompileResult,
    hir, mir, parse, sema, specialize, thir,
};
use std::time::{Duration, Instant};

pub mod bench_collector;
pub mod config;
pub mod context;
pub mod entry;
pub mod harness;
pub mod test_collector;

pub struct Compiler<'state> {
    pub context: GlobalContext<'state>,
}

#[derive(Debug, Clone)]
struct PhaseTiming {
    name: String,
    duration: Duration,
}

#[derive(Debug, Default, Clone)]
struct TimingReport {
    phases: Vec<PhaseTiming>,
}

impl TimingReport {
    fn push_elapsed(&mut self, name: &'static str, started_at: Instant) {
        self.phases.push(PhaseTiming {
            name: name.into(),
            duration: started_at.elapsed(),
        });
    }

    fn push_duration(&mut self, name: impl Into<String>, duration: Duration) {
        self.phases.push(PhaseTiming {
            name: name.into(),
            duration,
        });
    }

    fn push_codegen(
        &mut self,
        prefix: &str,
        entry: &str,
        timings: codegen::llvm::CodegenPhaseTimings,
    ) {
        for (phase, duration) in [
            ("setup", timings.module_setup),
            ("declare_instances", timings.declare_instances),
            ("lower_instances", timings.lower_instances),
            (entry, timings.emit_entry_or_harness),
            ("verify", timings.verify),
            ("optimize_ir", timings.optimize_ir),
            ("emit_artifact", timings.emit_artifact),
        ] {
            self.push_duration(format!("{prefix}.{phase}"), duration);
        }
    }

    fn emit(&self, package_name: &str, mode: &str, total: Duration) {
        eprintln!("Timings – {} ({})", package_name, mode);
        for phase in &self.phases {
            eprintln!(
                "  {:<30} {:>9.3} ms",
                phase.name,
                phase.duration.as_secs_f64() * 1000.0
            );
        }
        eprintln!("  {:<30} {:>9.3} ms", "total", total.as_secs_f64() * 1000.0);
    }
}

pub enum CompilationKind {
    Package,
    Executable,
}

impl<'state> Compiler<'state> {
    pub fn new(
        context: &'state CompilerContext<'state>,
        config: &'state Config,
    ) -> Compiler<'state> {
        Compiler {
            context: GlobalContext::new(context, config),
        }
    }
}

enum CompilationMode<'a> {
    Build,
    Emit,
    Test(&'a test_collector::TestSelection),
    Bench(&'a bench_collector::BenchmarkSelection),
}

impl CompilationMode<'_> {
    fn name(&self) -> &'static str {
        match self {
            Self::Build => "build",
            Self::Emit => "emit",
            Self::Test(_) => "test",
            Self::Bench(_) => "bench",
        }
    }
}

impl<'state> Compiler<'state> {
    pub fn build(&mut self) -> CompileResult<Option<std::path::PathBuf>> {
        self.compile(CompilationMode::Build)
            .map(|(_, executable)| executable)
    }

    /// Compile the package into its selected module artifact without linking.
    pub fn emit_module(&mut self) -> CompileResult<ModuleArtifact> {
        self.compile(CompilationMode::Emit)
            .map(|(artifact, _)| artifact)
    }

    /// Compile selected tests with a generated test harness as the entry point.
    pub fn test(
        &mut self,
        selection: &test_collector::TestSelection,
    ) -> CompileResult<Option<std::path::PathBuf>> {
        self.compile(CompilationMode::Test(selection))
            .map(|(_, executable)| executable)
    }

    /// Compile selected benchmarks with a generated benchmark harness.
    pub fn bench(
        &mut self,
        selection: &bench_collector::BenchmarkSelection,
    ) -> CompileResult<Option<std::path::PathBuf>> {
        self.compile(CompilationMode::Bench(selection))
            .map(|(_, executable)| executable)
    }

    fn compile(
        &mut self,
        mode: CompilationMode<'_>,
    ) -> CompileResult<(ModuleArtifact, Option<std::path::PathBuf>)> {
        let total_started_at = Instant::now();
        let mut timings = TimingReport::default();
        let result = (|| {
            let (package, results) = self.analyze_with_timings(&mut timings)?;
            let phase_started_at = Instant::now();
            let (entry, codegen_phase, entry_phase) = match mode {
                CompilationMode::Build | CompilationMode::Emit => (
                    codegen::llvm::PackageEntry::Main,
                    "codegen.llvm",
                    "emit_entry",
                ),
                CompilationMode::Test(selection) => {
                    let discovered = test_collector::collect_tests(&package, self.context)?;
                    let tests = test_collector::filter_tests(discovered, selection);
                    timings.push_elapsed("test.collect", phase_started_at);
                    (
                        codegen::llvm::PackageEntry::Tests(tests),
                        "codegen.llvm_test",
                        "emit_harness",
                    )
                }
                CompilationMode::Bench(selection) => {
                    let discovered = bench_collector::collect_benchmarks(&package, self.context)?;
                    let benchmarks = bench_collector::filter_benchmarks(discovered, selection);
                    timings.push_elapsed("bench.collect", phase_started_at);
                    (
                        codegen::llvm::PackageEntry::Benchmarks(benchmarks),
                        "codegen.llvm_bench",
                        "emit_harness",
                    )
                }
            };

            let thir = self.build_semantic_thir_with_timings(&package, results, &mut timings)?;
            let phase_started_at = Instant::now();
            let package = mir::package::build_package(thir, self.context)?;
            timings.push_elapsed("mir.build", phase_started_at);

            let phase_started_at = Instant::now();
            specialize::collect::collect_instances(package, self.context);
            timings.push_elapsed("specialize.collect_instances", phase_started_at);

            let phase_started_at = Instant::now();
            let (artifact, codegen_timings) =
                codegen::llvm::emit_package_with_timings(package, self.context, entry)?;
            timings.push_elapsed(codegen_phase, phase_started_at);
            timings.push_codegen(codegen_phase, entry_phase, codegen_timings);

            // Some monomorphization errors are reported through diagnostics
            // rather than Result. Never link an artifact after those errors.
            self.context.dcx().ok()?;
            let executable = if matches!(mode, CompilationMode::Emit) {
                None
            } else {
                if artifact.kind != ModuleArtifactKind::Object {
                    self.context.dcx().emit_error(
                        format!(
                            "cannot pass {} directly to the native linker",
                            artifact.kind.display_name()
                        ),
                        None,
                    );
                    return Err(crate::error::ReportedError);
                }
                let phase_started_at = Instant::now();
                let executable = codegen::link::link_executable(self.context)?;
                timings.push_elapsed("link.executable", phase_started_at);
                executable
            };
            Ok((artifact, executable))
        })();
        if self.context.config.debug.timings {
            timings.emit(
                &self.context.config.name,
                mode.name(),
                total_started_at.elapsed(),
            );
        }
        result
    }

    pub fn check(&mut self) -> CompileResult<hir::Package> {
        let total_started_at = Instant::now();
        let package_name = self.context.config.name.to_string();
        let mut timings = TimingReport::default();

        let result = (|| -> CompileResult<hir::Package> {
            let (package, results) = self.analyze_with_timings(&mut timings)?;
            let thir = self.build_semantic_thir_with_timings(&package, results, &mut timings)?;

            let phase_started_at = Instant::now();
            let _ = mir::package::build_package(thir, self.context)?;
            timings.push_elapsed("mir.build", phase_started_at);
            Ok(package)
        })();

        if self.context.config.debug.timings {
            timings.emit(&package_name, "check", total_started_at.elapsed());
        }

        result
    }

    pub fn analyze(
        &mut self,
    ) -> CompileResult<(
        hir::Package,
        sema::tycheck::results::TypeCheckResults<'state>,
    )> {
        let mut timings = TimingReport::default();
        self.analyze_with_timings(&mut timings)
    }

    fn analyze_with_timings(
        &mut self,
        timings: &mut TimingReport,
    ) -> CompileResult<(
        hir::Package,
        sema::tycheck::results::TypeCheckResults<'state>,
    )> {
        let package = self.lower_to_hir_with_timings(timings, false)?;

        let phase_started_at = Instant::now();
        sema::validate::validate_package(&package, self.context)?;
        timings.push_elapsed("sema.validate", phase_started_at);

        let phase_started_at = Instant::now();
        let results = if self.context.config.debug.timings {
            let (results, typecheck_timings) =
                sema::tycheck::typecheck_package_with_timings(&package, self.context)?;
            for phase in typecheck_timings {
                timings.push_duration(phase.name, phase.duration);
            }
            results
        } else {
            sema::tycheck::typecheck_package(&package, self.context)?
        };
        timings.push_elapsed("sema.typecheck", phase_started_at);

        let phase_started_at = Instant::now();
        sema::validate::validate_post_typecheck(&package, self.context, &results)?;
        timings.push_elapsed("sema.validate_post", phase_started_at);

        if !self.context.config.harness_mode.is_enabled() {
            let phase_started_at = Instant::now();
            let _ = entry::validate_entry_point(&package, self.context)?;
            timings.push_elapsed("entry.validate", phase_started_at);
        }

        Ok((package, results))
    }

    #[cfg(test)]
    pub(crate) fn analyze_for_diagnostics(&mut self, build_mir: bool) -> CompileResult<()> {
        let mut timings = TimingReport::default();
        let package = self.lower_to_hir_with_timings(&mut timings, true)?;

        let phase_started_at = Instant::now();
        let _ = sema::validate::validate_package(&package, self.context);
        timings.push_elapsed("sema.validate", phase_started_at);

        let phase_started_at = Instant::now();
        let results = sema::tycheck::typecheck_package(&package, self.context).ok();
        timings.push_elapsed("sema.typecheck", phase_started_at);

        if let Some(results) = &results {
            let phase_started_at = Instant::now();
            let _ = sema::validate::validate_post_typecheck(&package, self.context, results);
            timings.push_elapsed("sema.validate_post", phase_started_at);

            if !self.context.config.harness_mode.is_enabled() {
                let phase_started_at = Instant::now();
                let _ = entry::validate_entry_point(&package, self.context);
                timings.push_elapsed("entry.validate", phase_started_at);
            }

            if build_mir {
                let phase_started_at = Instant::now();
                if let Ok(thir) =
                    self.build_semantic_thir_with_timings(&package, results.clone(), &mut timings)
                {
                    let _ = mir::package::build_package(thir, self.context);
                }
                timings.push_elapsed("mir.build", phase_started_at);
            }
        }

        Ok(())
    }

    fn lower_to_hir_with_timings(
        &mut self,
        timings: &mut TimingReport,
        tolerate_std_item_errors: bool,
    ) -> CompileResult<hir::Package> {
        {
            let mut table = self.context.store.package_mapping.borrow_mut();
            table.insert(
                self.context.config.identifier.clone(),
                self.context.config.index,
            );
        }
        {
            self.context
                .cache_package_ident(self.context.config.identifier.clone());
        }
        if self.context.config.is_std_provider {
            self.context
                .store
                .std_provider_index
                .set(Some(self.context.config.index));
        }

        // Tokenization & Parsing
        // Get target triple for file-level cfg evaluation
        let triple = self.context.store.target_layout.triple();
        let triple_str = triple.as_str().to_str().unwrap_or("");

        let phase_started_at = Instant::now();
        let package = if self.context.config.is_script {
            parse::lexer::tokenize_single_file(
                self.context.config.src.clone(),
                &self.context.dcx,
                Some(triple_str),
            )?
        } else {
            parse::lexer::tokenize_package(
                self.context.config.src.clone(),
                &self.context.dcx,
                Some(triple_str),
            )?
        };
        timings.push_elapsed("parse.tokenize", phase_started_at);

        let target = cfg_eval::target_info(self.context);

        let phase_started_at = Instant::now();
        let mut package = parse::parser::parse_package(package, &self.context.dcx)?;
        timings.push_elapsed("parse.ast", phase_started_at);

        // AST passes
        let phase_started_at = Instant::now();
        cfg_eval::filter_package(&mut package, &target, self.context);
        timings.push_elapsed("cfg.filter", phase_started_at);

        let phase_started_at = Instant::now();
        let resolution_output = sema::resolve::resolve_package(&package, self.context)?;
        timings.push_elapsed("sema.resolve", phase_started_at);

        let phase_started_at = Instant::now();
        let output = self
            .context
            .store
            .arenas
            .resolution_outputs
            .alloc(resolution_output);
        {
            let mut table = self.context.store.resolution_outputs.borrow_mut();
            table.insert(self.context.config.index, output);
        }
        let std_items = sema::std_items::collect_std_items(&package, self.context, output);
        if let Some(items) = if tolerate_std_item_errors {
            std_items.ok().flatten()
        } else {
            std_items?
        } {
            self.context
                .store
                .std_items
                .borrow_mut()
                .replace((self.context.package_index(), items));
        }
        let package = ast_lowering::lower_package(package, self.context, output)?;
        timings.push_elapsed("hir.lower", phase_started_at);
        Ok(package)
    }

    fn build_semantic_thir_with_timings(
        &mut self,
        package: &hir::Package,
        results: sema::tycheck::results::TypeCheckResults<'state>,
        timings: &mut TimingReport,
    ) -> CompileResult<thir::ThirPackage<'state>> {
        let phase_started_at = Instant::now();
        let thir = thir::package::build_package(package, self.context, results)?;
        timings.push_elapsed("thir.build", phase_started_at);
        Ok(thir)
    }
}
