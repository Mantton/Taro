use crate::{
    compile::context::Gcx,
    hir::Abi,
    mir::{CallGcEffect, ConstantKind, Operand},
    runtime_abi::{RuntimeGcEffect, gc_effect_for_symbol},
};

/// Classify a MIR call from its language ABI and the exhaustive runtime ABI
/// registry. Indirect and virtual managed calls conservatively establish a
/// managed safepoint; C and intrinsic calls are non-collecting unless the
/// declaration uses Taro's explicit blocking ABI.
pub fn classify_call_gc_effect(
    gcx: Gcx<'_>,
    function: &Operand<'_>,
) -> Result<CallGcEffect, String> {
    let Operand::Constant(constant) = function else {
        return Ok(CallGcEffect::ManagedSafepoint);
    };
    let ConstantKind::Function(definition, _, _) = constant.value else {
        return Ok(CallGcEffect::ManagedSafepoint);
    };

    match gcx.get_signature(definition).abi {
        Some(Abi::Intrinsic | Abi::C) => Ok(CallGcEffect::NoGc),
        Some(Abi::Blocking) => Ok(CallGcEffect::BlockingSafepoint),
        Some(Abi::Runtime) => {
            let symbol = gcx.definition_symbol_or_fallback(definition);
            let symbol = gcx.symbol_text(symbol);
            let effect = gc_effect_for_symbol(symbol.as_str()).ok_or_else(|| {
                format!("runtime ABI entry `{symbol}` is missing a GC effect classification")
            })?;
            Ok(match effect {
                RuntimeGcEffect::NoGc => CallGcEffect::NoGc,
                RuntimeGcEffect::RuntimeSafepoint => CallGcEffect::RuntimeSafepoint,
                RuntimeGcEffect::BlockingSafepoint => CallGcEffect::BlockingSafepoint,
            })
        }
        None => Ok(CallGcEffect::ManagedSafepoint),
    }
}
