use crate::{
    ast_lowering, cfg, cfg_eval, codegen,
    compile::{
        config::Config,
        context::{CompilerContext, GlobalContext},
    },
    error::CompileResult,
    hir, mir, parse, sema, specialize, thir,
};

pub mod config;
pub mod context;
pub mod entry;

pub struct Compiler<'state> {
    pub context: GlobalContext<'state>,
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
        let (package, results) = self.analyze()?;
        let thir = thir::package::build_package(&package, self.context, results)?;
        let package = mir::package::build_package(thir, self.context)?;
        specialize::collect::collect_instances(package, self.context);
        let _ = codegen::llvm::emit_package(package, self.context)?;
        let exe = codegen::link::link_executable(self.context)?;
        Ok(exe)
    }

    pub fn check(&mut self) -> CompileResult<hir::Package> {
        let (package, _) = self.analyze()?;
        Ok(package)
    }

    pub fn analyze(
        &mut self,
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
        // Tokenization & Parsing
        // Get target triple for file-level cfg evaluation
        let triple = self.context.store.target_layout.triple();
        let triple_str = triple.as_str().to_str().unwrap_or("");
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
        let mut target = cfg::TargetInfo::from_triple(triple_str);
        target.profile = match self.context.config.profile {
            crate::compile::config::BuildProfile::Debug => "debug".to_string(),
            crate::compile::config::BuildProfile::Release => "release".to_string(),
        };

        let mut package = parse::parser::parse_package(package, &self.context.dcx)?;
        // AST Passes
        cfg_eval::filter_package(&mut package, &target);
        let resolution_output = sema::resolve::resolve_package(&package, self.context)?;
        let package = ast_lowering::lower_package(package, self.context, &resolution_output)?;
        {
            let mut table = self.context.store.resolution_outputs.borrow_mut();
            let output = self
                .context
                .store
                .arenas
                .resolution_outputs
                .alloc(resolution_output);
            table.insert(self.context.config.index, output);
        }

        sema::validate::validate_package(&package, self.context)?;
        let results = sema::tycheck::typecheck_package(&package, self.context)?;
        sema::validate::validate_post_typecheck(&package, self.context, &results)?;
        let _ = entry::validate_entry_point(&package, self.context)?;
        Ok((package, results))
    }
}
