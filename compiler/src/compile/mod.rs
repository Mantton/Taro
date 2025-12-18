use crate::{
    ast_lowering, codegen,
    compile::{
        config::Config,
        context::{CompilerContext, GlobalContext},
    },
    error::CompileResult,
    hir, mir, parse, sema, thir,
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
        let package = self.analyze()?;
        let thir = thir::package::build_package(&package, self.context)?;
        let package = mir::package::build_package(thir, self.context)?;
        return Ok(None);
        let _obj = codegen::llvm::emit_package(package, self.context)?;
        let exe = codegen::link::link_executable(self.context)?;
        Ok(exe)
    }

    pub fn check(&mut self) -> CompileResult<hir::Package> {
        self.analyze()
    }

    pub fn analyze(&mut self) -> CompileResult<hir::Package> {
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
        let package =
            parse::lexer::tokenize_package(self.context.config.src.clone(), &self.context.dcx)?;
        let package = parse::parser::parse_package(package, &self.context.dcx)?;
        // AST Passes
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
        sema::tycheck::typecheck_package(&package, self.context)?;
        let _ = entry::validate_entry_point(&package, self.context)?;
        Ok(package)
    }
}
