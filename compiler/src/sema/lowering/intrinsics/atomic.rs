//! Exact declarations for unsafe scalar atomic intrinsics.
use crate::{
    compile::context::Gcx,
    hir::{Abi, DefinitionID},
    sema::models::TyKind,
};

pub(crate) fn arity(name: &str) -> Option<usize> {
    Some(match name {
        "__intrinsic_atomic_load" => 1,
        "__intrinsic_atomic_store" | "__intrinsic_atomic_swap" | "__intrinsic_atomic_add" => 2,
        "__intrinsic_atomic_compare_exchange" => 3,
        _ => return None,
    })
}

pub(crate) fn valid(gcx: Gcx<'_>, id: DefinitionID) -> bool {
    let name = gcx.definition_ident(id).symbol;
    let Some(arity) = arity(name.as_str()) else {
        return false;
    };
    let sig = gcx.get_signature(id);
    let generics = gcx.generics_of(id);
    if sig.abi != Some(Abi::Intrinsic)
        || sig.is_variadic
        || !gcx.definition_is_unsafe(id)
        || gcx.definition_is_async(id)
        || generics.parent.is_some()
        || generics.parameters.len() != 1
        || sig.inputs.len() != arity
    {
        return false;
    }
    let TyKind::Pointer(element, _) = sig.inputs[0].ty.kind() else {
        return false;
    };
    if !matches!(element.kind(), TyKind::Parameter(p) if p.index == 0)
        || sig.inputs[1..].iter().any(|arg| arg.ty != element)
    {
        return false;
    }
    sig.output
        == match name.as_str() {
            "__intrinsic_atomic_store" => gcx.types.void,
            "__intrinsic_atomic_compare_exchange" => gcx.types.bool,
            _ => element,
        }
}

#[cfg(test)]
mod tests {
    #[test]
    fn malformed_or_safe_atomic_intrinsics_are_rejected() {
        for declaration in [
            "func __intrinsic_atomic_load[T](_ slot: *T) -> T",
            "unsafe func __intrinsic_atomic_store[T](_ slot: *T, _ value: bool)",
            "unsafe func __intrinsic_atomic_compare_exchange[T](_ slot: *T, _ expected: T, _ desired: T) -> T",
        ] {
            let diagnostics = crate::test_support::analyze_script_diagnostics(&format!(
                "extern \"taro_intrinsic\" {{ {declaration}; }}\nfunc main() {{}}"
            ));
            assert!(
                diagnostics
                    .iter()
                    .any(|d| d.message.contains("atomic intrinsic")),
                "{diagnostics:?}"
            );
        }
    }
}
