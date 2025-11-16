use std::rc::Rc;

use crate::{
    compile::{config::Config, state::CompilerState},
    diagnostics::DiagCtx,
    error::CompileResult,
    parse, sema,
};

pub mod config;
pub mod context;
pub mod state;

pub struct Compiler {
    pub state: CompilerState,
}

pub enum CompilationKind {
    Package,
    Executable,
}

impl Compiler {
    pub fn new(config: Config, dcx: Rc<DiagCtx>) -> Compiler {
        Compiler {
            state: CompilerState::new(config, dcx),
        }
    }
}

impl Compiler {
    pub fn build(&mut self) -> CompileResult<()> {
        let package =
            parse::lexer::tokenize_package(self.state.config.src.clone(), &self.state.dcx)?;
        let package = parse::parser::parse_package(package, &self.state.dcx)?;
        sema::resolve::resolve_package(&package, &self.state)?;

        Ok(())
    }
}

impl Compiler {}
