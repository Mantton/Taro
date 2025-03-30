use taroc_context::GlobalContext;
use taroc_error::CompileResult;

pub fn run(
    mut package: taroc_ast::Package,
    context: GlobalContext,
) -> CompileResult<taroc_hir::Package> {
    taroc_ast_lowering::run(package, context)
}

// Validate functions
// validate extensions & conformances
// validate namespaces and extern
// validate default type parameters
// validate interfaces may only be nested in modular spaces (Namespace, Top Level)
