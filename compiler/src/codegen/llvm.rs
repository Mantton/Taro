use crate::{compile::context::GlobalContext, error::CompileResult, mir};
use inkwell::context::Context;

/// Build a minimal LLVM module for the current package and cache its IR.
/// This is intentionally small: no full lowering yet, just module creation.
pub fn emit_package<'ctx>(
    package: &'ctx mir::MirPackage<'ctx>,
    gcx: GlobalContext<'ctx>,
) -> CompileResult<()> {
    let context = Context::create();
    let module = context.create_module(&gcx.config.identifier);

    // Placeholder: we could add declarations based on MIR in the future.
    let ir = module.print_to_string().to_string();
    gcx.cache_llvm_ir(ir);
    Ok(())
}
