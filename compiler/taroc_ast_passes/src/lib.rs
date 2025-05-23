use taroc_error::CompileResult;
use taroc_sema::GlobalContext;

pub fn run(
    package: taroc_ast::Package,
    context: GlobalContext,
) -> CompileResult<taroc_hir::Package> {
    taroc_ast_lowering::run(package, context)
}

// Validate functions
// validate extensions & conformances
// validate namespaces and extern
// validate default type parameters
// validate interfaces may only be nested in modular spaces (Namespace, Top Level)
// validate opaque type usage (some T), isolate to computed properties and functions
// validate ternary types
