use crate::{
    ast_lowering, cfg, cfg_eval, codegen,
    compile::{
        config::Config,
        context::{CompilerContext, GlobalContext},
    },
    error::CompileResult,
    hir, mir, parse, sema, specialize, thir,
};
use rustc_hash::FxHashSet;
use std::time::{Duration, Instant};

pub mod config;
pub mod context;
pub mod entry;
pub mod test_collector;

pub struct Compiler<'state> {
    pub context: GlobalContext<'state>,
}

pub struct IdeAnalysis<'state> {
    pub package: hir::Package,
    pub results: Option<sema::tycheck::results::TypeCheckResults<'state>>,
    pub status: IdeAnalysisStatus,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IdeAnalysisMode {
    OnType,
    OnSave,
}

#[derive(Debug, Clone, Copy, Default)]
pub struct IdeAnalysisStatus {
    pub hir_available: bool,
    pub typed_available: bool,
}

#[derive(Debug, Clone)]
struct PhaseTiming {
    name: &'static str,
    duration: Duration,
}

#[derive(Debug, Default, Clone)]
struct TimingReport {
    phases: Vec<PhaseTiming>,
}

impl TimingReport {
    fn push_elapsed(&mut self, name: &'static str, started_at: Instant) {
        self.phases.push(PhaseTiming {
            name,
            duration: started_at.elapsed(),
        });
    }

    fn push_duration(&mut self, name: &'static str, duration: Duration) {
        self.phases.push(PhaseTiming { name, duration });
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

impl<'state> Compiler<'state> {
    pub fn build(&mut self) -> CompileResult<Option<std::path::PathBuf>> {
        let total_started_at = Instant::now();
        let package_name = self.context.config.name.to_string();
        let mut timings = TimingReport::default();

        let result = (|| -> CompileResult<Option<std::path::PathBuf>> {
            let (package, results) = self.analyze_with_timings(&mut timings)?;

            let thir = self.build_semantic_thir_with_timings(&package, results, &mut timings)?;

            let phase_started_at = Instant::now();
            let package = mir::package::build_package(thir, self.context)?;
            timings.push_elapsed("mir.build", phase_started_at);

            let phase_started_at = Instant::now();
            specialize::collect::collect_instances(package, self.context);
            timings.push_elapsed("specialize.collect_instances", phase_started_at);

            let compiled_before_codegen = self.context.store.compiled_instances.borrow().clone();

            let phase_started_at = Instant::now();
            let (_, codegen_timings) =
                codegen::llvm::emit_package_with_timings(package, self.context)?;
            timings.push_elapsed("codegen.llvm", phase_started_at);
            timings.push_duration("codegen.llvm.setup", codegen_timings.module_setup);
            timings.push_duration(
                "codegen.llvm.declare_instances",
                codegen_timings.declare_instances,
            );
            timings.push_duration(
                "codegen.llvm.lower_instances",
                codegen_timings.lower_instances,
            );
            timings.push_duration(
                "codegen.llvm.emit_entry",
                codegen_timings.emit_entry_or_harness,
            );
            timings.push_duration("codegen.llvm.verify", codegen_timings.verify);
            timings.push_duration(
                "codegen.llvm.function_passes",
                codegen_timings.function_passes,
            );
            timings.push_duration("codegen.llvm.emit_object", codegen_timings.emit_object);

            let compiled_after_codegen = self.context.store.compiled_instances.borrow().clone();
            let emitted_instances = compiled_after_codegen
                .difference(&compiled_before_codegen)
                .cloned()
                .collect();
            self.context
                .cache_emitted_instances(self.context.package_index(), emitted_instances);

            let phase_started_at = Instant::now();
            let exe = codegen::link::link_executable(self.context)?;
            timings.push_elapsed("link.executable", phase_started_at);

            Ok(exe)
        })();

        if self.context.config.debug.timings {
            timings.emit(&package_name, "build", total_started_at.elapsed());
        }

        result
    }

    /// Build in test mode: compile all code, discover tests, and generate
    /// a test harness as the entry point instead of the normal main.
    pub fn test(
        &mut self,
        selection: &test_collector::TestSelection,
    ) -> CompileResult<Option<std::path::PathBuf>> {
        let total_started_at = Instant::now();
        let package_name = self.context.config.name.to_string();
        let mut timings = TimingReport::default();

        let result = (|| -> CompileResult<Option<std::path::PathBuf>> {
            let (package, results) = self.analyze_with_timings(&mut timings)?;

            // Collect tests from HIR (needs type info from analysis)
            let phase_started_at = Instant::now();
            let discovered_tests = test_collector::collect_tests(&package, self.context)?;
            let tests = test_collector::filter_tests(discovered_tests, selection);
            timings.push_elapsed("test.collect", phase_started_at);

            let thir = self.build_semantic_thir_with_timings(&package, results, &mut timings)?;

            let phase_started_at = Instant::now();
            let package = mir::package::build_package(thir, self.context)?;
            timings.push_elapsed("mir.build", phase_started_at);

            let phase_started_at = Instant::now();
            specialize::collect::collect_instances(package, self.context);
            timings.push_elapsed("specialize.collect_instances", phase_started_at);

            let compiled_before_codegen = self.context.store.compiled_instances.borrow().clone();

            let phase_started_at = Instant::now();
            let (_, codegen_timings) =
                codegen::llvm::emit_test_package_with_timings(package, self.context, &tests)?;
            timings.push_elapsed("codegen.llvm_test", phase_started_at);
            timings.push_duration("codegen.llvm_test.setup", codegen_timings.module_setup);
            timings.push_duration(
                "codegen.llvm_test.declare_instances",
                codegen_timings.declare_instances,
            );
            timings.push_duration(
                "codegen.llvm_test.lower_instances",
                codegen_timings.lower_instances,
            );
            timings.push_duration(
                "codegen.llvm_test.emit_harness",
                codegen_timings.emit_entry_or_harness,
            );
            timings.push_duration("codegen.llvm_test.verify", codegen_timings.verify);
            timings.push_duration(
                "codegen.llvm_test.function_passes",
                codegen_timings.function_passes,
            );
            timings.push_duration("codegen.llvm_test.emit_object", codegen_timings.emit_object);

            let compiled_after_codegen = self.context.store.compiled_instances.borrow().clone();
            let emitted_instances = compiled_after_codegen
                .difference(&compiled_before_codegen)
                .cloned()
                .collect();
            self.context
                .cache_emitted_instances(self.context.package_index(), emitted_instances);

            let phase_started_at = Instant::now();
            let exe = codegen::link::link_executable(self.context)?;
            timings.push_elapsed("link.executable", phase_started_at);

            Ok(exe)
        })();

        if self.context.config.debug.timings {
            timings.emit(&package_name, "test", total_started_at.elapsed());
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

    /// Compile dependency semantic state (HIR/THIR/MIR/specializations) without
    /// producing a new object file. This is used to reuse cached dependency
    /// objects while still making dependency semantics available to downstream
    /// packages in the current session.
    pub fn prepare_dependency_reuse(&mut self) -> CompileResult<()> {
        let total_started_at = Instant::now();
        let package_name = self.context.config.name.to_string();
        let mut timings = TimingReport::default();

        let result = (|| -> CompileResult<()> {
            let (package, results) = self.analyze_with_timings(&mut timings)?;

            let thir = self.build_semantic_thir_with_timings(&package, results, &mut timings)?;

            let phase_started_at = Instant::now();
            let package = mir::package::build_package(thir, self.context)?;
            timings.push_elapsed("mir.build", phase_started_at);

            let phase_started_at = Instant::now();
            specialize::collect::collect_instances(package, self.context);
            timings.push_elapsed("specialize.collect_instances", phase_started_at);

            let emitted_instances = self.predicted_emitted_instances();
            for instance in emitted_instances.iter().copied() {
                self.context.mark_instance_compiled(instance);
            }
            self.context
                .cache_emitted_instances(self.context.package_index(), emitted_instances);

            Ok(())
        })();

        if self.context.config.debug.timings {
            timings.emit(
                &package_name,
                "prepare_dependency_reuse",
                total_started_at.elapsed(),
            );
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

    pub fn analyze_for_ide(&mut self, mode: IdeAnalysisMode) -> CompileResult<IdeAnalysis<'state>> {
        let mut timings = TimingReport::default();
        self.analyze_for_ide_with_timings(mode, &mut timings)
    }

    fn predicted_emitted_instances(&self) -> FxHashSet<specialize::Instance<'state>> {
        let mut emitted = FxHashSet::default();
        let current_pkg = self.context.package_index();

        for instance in self.context.specializations_of(current_pkg) {
            let specialize::InstanceKind::Item(def_id) = instance.kind() else {
                continue;
            };

            if matches!(
                self.context.get_signature(def_id).abi,
                Some(hir::Abi::Intrinsic | hir::Abi::C)
            ) {
                continue;
            }

            let has_mir_body = {
                let packages = self.context.store.mir_packages.borrow();
                packages
                    .get(&def_id.package())
                    .is_some_and(|pkg| pkg.functions.contains_key(&def_id))
            };

            if has_mir_body {
                emitted.insert(instance);
            }
        }

        emitted
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

        if !self.context.config.test_mode {
            let phase_started_at = Instant::now();
            let _ = entry::validate_entry_point(&package, self.context)?;
            timings.push_elapsed("entry.validate", phase_started_at);
        }

        Ok((package, results))
    }

    fn analyze_for_ide_with_timings(
        &mut self,
        mode: IdeAnalysisMode,
        timings: &mut TimingReport,
    ) -> CompileResult<IdeAnalysis<'state>> {
        let package = self.lower_to_hir_with_timings(timings, true)?;

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

            if !self.context.config.test_mode {
                let phase_started_at = Instant::now();
                let _ = entry::validate_entry_point(&package, self.context);
                timings.push_elapsed("entry.validate", phase_started_at);
            }

            if mode == IdeAnalysisMode::OnSave {
                let phase_started_at = Instant::now();
                if let Ok(thir) =
                    self.build_semantic_thir_with_timings(&package, results.clone(), timings)
                {
                    let _ = mir::package::build_package(thir, self.context);
                }
                timings.push_elapsed("mir.build", phase_started_at);
            }
        }

        Ok(IdeAnalysis {
            package,
            status: IdeAnalysisStatus {
                hir_available: true,
                typed_available: results.is_some(),
            },
            results,
        })
    }

    fn lower_to_hir_with_timings(
        &mut self,
        timings: &mut TimingReport,
        ide_mode: bool,
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

        let mut target = cfg::TargetInfo::from_triple(triple_str);
        target.profile = match self.context.config.profile {
            crate::compile::config::BuildProfile::Debug => "debug".to_string(),
            crate::compile::config::BuildProfile::Release => "release".to_string(),
        };
        target.test_mode = self.context.config.test_mode;

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
        if let Some(items) = if ide_mode {
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
