use taroc_context::GlobalContext;
use taroc_error::CompileResult;

pub fn run(package: &taroc_hir::Package, context: GlobalContext) -> CompileResult<()> {
    CheckRecursiveTypes::run(context)?;
    CheckInterfaceImplementation::run(context)?;
    context.diagnostics.report()
}

/// Check Recursive Types
/// Check Interface Implementation
/// Checks if type correctly implement an interface
struct CheckRecursiveTypes<'ctx> {
    context: GlobalContext<'ctx>,
}

impl<'ctx> CheckRecursiveTypes<'ctx> {
    fn new(context: GlobalContext<'ctx>) -> CheckRecursiveTypes<'ctx> {
        CheckRecursiveTypes { context }
    }

    fn run<'a>(context: GlobalContext<'ctx>) -> CompileResult<()> {
        let mut actor = CheckRecursiveTypes::new(context);

        context.diagnostics.report()
    }
}

/// Check Interface Implementation
/// Checks if type correctly implement an interface
struct CheckInterfaceImplementation<'ctx> {
    context: GlobalContext<'ctx>,
}

impl<'ctx> CheckInterfaceImplementation<'ctx> {
    fn new(context: GlobalContext<'ctx>) -> CheckInterfaceImplementation<'ctx> {
        CheckInterfaceImplementation { context }
    }

    fn run<'a>(context: GlobalContext<'ctx>) -> CompileResult<()> {
        let mut actor = CheckInterfaceImplementation::new(context);
        context.diagnostics.report()
    }
}
