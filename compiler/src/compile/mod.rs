use crate::{
    ast_lowering, cfg, cfg_eval, codegen,
    compile::{
        config::Config,
        context::{CompilerContext, GlobalContext},
    },
    error::CompileResult,
    hir, mir, parse, sema, specialize, thir,
};
use std::time::{Duration, Instant};

pub mod config;
pub mod context;
pub mod entry;
pub mod test_collector;

pub struct Compiler<'state> {
    pub context: GlobalContext<'state>,
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

            let phase_started_at = Instant::now();
            let thir = thir::package::build_package(&package, self.context, results)?;
            timings.push_elapsed("thir.build", phase_started_at);

            let phase_started_at = Instant::now();
            let package = mir::package::build_package(thir, self.context)?;
            timings.push_elapsed("mir.build", phase_started_at);

            let phase_started_at = Instant::now();
            specialize::collect::collect_instances(package, self.context);
            timings.push_elapsed("specialize.collect_instances", phase_started_at);

            let phase_started_at = Instant::now();
            let _ = codegen::llvm::emit_package(package, self.context)?;
            timings.push_elapsed("codegen.llvm", phase_started_at);

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
    pub fn test(&mut self) -> CompileResult<Option<std::path::PathBuf>> {
        let total_started_at = Instant::now();
        let package_name = self.context.config.name.to_string();
        let mut timings = TimingReport::default();

        let result = (|| -> CompileResult<Option<std::path::PathBuf>> {
            let (package, results) = self.analyze_with_timings(&mut timings)?;

            // Collect tests from HIR (needs type info from analysis)
            let phase_started_at = Instant::now();
            let tests = test_collector::collect_tests(&package, self.context)?;
            timings.push_elapsed("test.collect", phase_started_at);
            if tests.is_empty() {
                eprintln!("warning: no test functions found");
                return Ok(None);
            }

            let phase_started_at = Instant::now();
            let thir = thir::package::build_package(&package, self.context, results)?;
            timings.push_elapsed("thir.build", phase_started_at);

            let phase_started_at = Instant::now();
            let package = mir::package::build_package(thir, self.context)?;
            timings.push_elapsed("mir.build", phase_started_at);

            let phase_started_at = Instant::now();
            specialize::collect::collect_instances(package, self.context);
            timings.push_elapsed("specialize.collect_instances", phase_started_at);

            let phase_started_at = Instant::now();
            let _ = codegen::llvm::emit_test_package(package, self.context, &tests)?;
            timings.push_elapsed("codegen.llvm_test", phase_started_at);

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
            let (package, _) = self.analyze_with_timings(&mut timings)?;
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
        let package = ast_lowering::lower_package(package, self.context, output)?;
        timings.push_elapsed("hir.lower", phase_started_at);

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
}
