use crate::{
    ast_lowering,
    compile::{
        config::Config,
        context::{CompilerContext, GlobalContext},
    },
    error::CompileResult,
    parse, sema,
};

pub mod config;
pub mod context;

pub struct Compiler<'state> {
    pub context: GlobalContext<'state>,
}

pub enum CompilationKind {
    Package,
    Executable,
}

impl<'state> Compiler<'state> {
    pub fn new(context: &'state CompilerContext, config: &'state Config) -> Compiler<'state> {
        Compiler {
            context: GlobalContext::new(context, config),
        }
    }
}

impl<'state> Compiler<'state> {
    pub fn build(&mut self) -> CompileResult<()> {
        // Tokenization & Parsing
        let package =
            parse::lexer::tokenize_package(self.context.config.src.clone(), &self.context.dcx)?;
        let package = parse::parser::parse_package(package, &self.context.dcx)?;
        // AST Passes
        let resolution_output = sema::resolve::resolve_package(&package, self.context)?;
        // HIR Construction
        let package = ast_lowering::lower_package(package, self.context, resolution_output)?;
        // HIR Passes
        sema::validate::validate_package(&package, self.context)?;
        sema::tycheck::check_package(&package, self.context)?;
        Ok(())
    }
}
