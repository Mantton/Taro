use std::rc::Rc;

use crate::{
    ast_lowering,
    compile::{
        config::Config,
        state::{CompilerContext, CompilerState},
    },
    diagnostics::DiagCtx,
    error::CompileResult,
    parse, sema,
};

pub mod config;
pub mod global;
pub mod state;

pub struct Compiler<'state> {
    pub state: CompilerState<'state>,
}

pub enum CompilationKind {
    Package,
    Executable,
}

impl<'state> Compiler<'state> {
    pub fn new(context: &'state CompilerContext) -> Compiler<'state> {
        Compiler {
            state: CompilerState::new(context),
        }
    }
}

impl<'state> Compiler<'state> {
    pub fn build(&mut self) -> CompileResult<()> {
        let package =
            parse::lexer::tokenize_package(self.state.config.src.clone(), &self.state.dcx)?;
        let package = parse::parser::parse_package(package, &self.state.dcx)?;
        sema::resolve::resolve_package(&package, self.state)?;
        let package = ast_lowering::lower_package(package, self.state)?;
        Ok(())
    }
}
