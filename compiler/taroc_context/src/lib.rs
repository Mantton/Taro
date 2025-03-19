use std::{env::current_dir, ops::Deref};
use taroc_diagnostics::{DiagnosticContext, DiagnosticLevel};
use taroc_span::SpannedMessage;

mod context;
mod models;
mod session;

pub use context::*;
pub use models::*;
pub use session::*;

#[derive(Copy, Clone)]
pub struct GlobalContext<'ctx> {
    context: &'ctx CompilerContext<'ctx>,
}

impl<'ctx> GlobalContext<'ctx> {
    pub fn new(context: &'ctx CompilerContext<'ctx>) -> GlobalContext<'ctx> {
        GlobalContext { context }
    }
}

impl<'ctx> Deref for GlobalContext<'ctx> {
    type Target = &'ctx CompilerContext<'ctx>;
    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &self.context
    }
}

pub struct CompilerContext<'ctx> {
    pub diagnostics: DiagnosticContext,
    pub store: ContextStore<'ctx>,
}

impl<'ctx> CompilerContext<'ctx> {
    pub fn new(arenas: &'ctx ContextArenas<'ctx>) -> CompilerContext<'ctx> {
        CompilerContext {
            diagnostics: DiagnosticContext::new(
                current_dir().expect("Expected Current Working Directory"),
            ),
            store: ContextStore::new(arenas),
        }
    }
}

pub fn with_global_context<T, F: for<'a> FnOnce(GlobalContext<'a>) -> T>(f: F) -> T {
    let arenas = ContextArenas::new();
    let context = CompilerContext::new(&arenas);
    let gcx = GlobalContext::new(&context);
    f(gcx)
}

#[derive(Debug, Default)]
pub struct WithDiagnostics<T> {
    pub value: T,
    messages: Vec<(DiagnosticLevel, SpannedMessage)>,
}

impl<T> WithDiagnostics<T> {
    fn message(&mut self, message: SpannedMessage, level: DiagnosticLevel) {
        self.messages.push((level, message));
    }
    pub fn error(&mut self, message: SpannedMessage) {
        self.message(message, DiagnosticLevel::Error);
    }
    pub fn warn(&mut self, message: SpannedMessage) {
        self.message(message, DiagnosticLevel::Warn);
    }
    pub fn info(&mut self, message: SpannedMessage) {
        self.message(message, DiagnosticLevel::Info);
    }
}

impl<T: Default> WithDiagnostics<T> {
    pub fn export(self, context: GlobalContext) -> T {
        for (level, message) in self.messages.into_iter() {
            context
                .diagnostics
                .message(message.message, message.span, level);
        }

        return self.value;
    }
}
