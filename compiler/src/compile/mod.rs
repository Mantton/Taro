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
    pub fn new(config: Config) -> Compiler {
        Compiler {
            state: CompilerState::new(config),
        }
    }
}

impl Compiler {
    pub fn build(&mut self) -> CompileResult<()> {
        let dcx = DiagCtx::new();
        let package = parse::lexer::tokenize_package(self.state.config.src.clone(), &dcx)?;
        let package = parse::parser::parse_package(package, &dcx)?;
        sema::resolve::resolve_package(&package)?;

        Ok(())
    }
}

impl Compiler {}
