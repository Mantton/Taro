use crate::{
    ast_lowering,
    compile::{
        config::Config,
        context::{CompilerContext, GlobalContext},
    },
    error::CompileResult,
    mir, parse, sema,
};

pub mod config;
pub mod context;
mod entry;

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
    pub fn build(&mut self) -> CompileResult<()> {
        {
            let mut table = self.context.store.package_mapping.borrow_mut();
            table.insert(
                self.context.config.identifier.clone(),
                self.context.config.index,
            );
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

        // HIR Construction
        // HIR Passes
        sema::validate::validate_package(&package, self.context)?;
        sema::tycheck::typecheck_package(&package, self.context)?;
        entry::validate_entry_point(&package, self.context)?;
        mir::package::build_package(&package, self.context)?;
        Ok(())
    }
}
