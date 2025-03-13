use std::{env::current_dir, ops::Deref};
use taroc_diagnostics::{DiagnosticContext, DiagnosticLevel};
use taroc_package::CompilerConfig;
use taroc_span::SpannedMessage;

#[derive(Copy, Clone)]
pub struct GlobalContext<'ctx> {
    context: &'ctx CompilerContext,
}

impl<'ctx> GlobalContext<'ctx> {
    pub fn new(context: &'ctx CompilerContext) -> GlobalContext<'ctx> {
        GlobalContext { context }
    }
}

impl<'ctx> Deref for GlobalContext<'ctx> {
    type Target = &'ctx CompilerContext;
    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &self.context
    }
}

pub struct CompilerContext {
    pub config: CompilerConfig,
    pub diagnostics: DiagnosticContext,
}

impl<'a> CompilerContext {
    pub fn new(config: CompilerConfig) -> CompilerContext {
        CompilerContext {
            config,
            diagnostics: DiagnosticContext::new(
                current_dir().expect("Expected Current Working Directory"),
            ),
        }
    }
}

pub fn with_global_context<T, F: for<'a> FnOnce(GlobalContext<'a>) -> T>(
    config: CompilerConfig,
    f: F,
) -> T {
    let context = CompilerContext::new(config);
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
