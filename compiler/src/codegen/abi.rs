use crate::sema::models::{LabeledFunctionSignature, Ty, TyKind};

/// ABI pass mode for a value in a lowered function signature.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PassMode {
    /// Value does not participate in ABI (e.g. zero-sized type / unit).
    Ignore,
    /// Value is passed/returned directly.
    Direct,
    /// Value is passed/returned indirectly via a pointer.
    Indirect { align: u32, size: u64 },
}

/// Minimal layout facts needed by ABI classification.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TypeLayout {
    pub size: u64,
    pub align: u32,
}

/// ABI info for one argument or return value.
#[derive(Debug, Clone, Copy)]
pub struct ArgAbi<'gcx> {
    pub ty: Ty<'gcx>,
    pub mode: PassMode,
}

/// ABI-lowered function signature.
#[derive(Debug, Clone)]
pub struct FnAbi<'gcx> {
    pub ret: ArgAbi<'gcx>,
    pub args: Vec<ArgAbi<'gcx>>,
    pub c_variadic: bool,
}

/// Temporary policy knob while introducing ABI classification incrementally.
#[derive(Debug, Clone, Copy)]
pub struct AbiPolicy {
    /// Enables using `PassMode::Indirect` for return values.
    pub enable_indirect_returns: bool,
    /// Size threshold for indirect return mode when enabled.
    pub indirect_return_threshold_bytes: u64,
    /// Enables using `PassMode::Indirect` for argument values.
    pub enable_indirect_args: bool,
    /// Size threshold for indirect argument mode when enabled.
    pub indirect_arg_threshold_bytes: u64,
}

impl Default for AbiPolicy {
    fn default() -> Self {
        AbiPolicy {
            // Phase A: keep behavior unchanged.
            enable_indirect_returns: false,
            indirect_return_threshold_bytes: 0,
            enable_indirect_args: false,
            indirect_arg_threshold_bytes: 0,
        }
    }
}

pub fn compute_fn_abi<'gcx>(
    sig: &LabeledFunctionSignature<'gcx>,
    layout_of: impl FnMut(Ty<'gcx>) -> Option<TypeLayout>,
    policy: AbiPolicy,
) -> FnAbi<'gcx> {
    let input_tys: Vec<_> = sig.inputs.iter().map(|param| param.ty).collect();
    compute_fn_abi_from_tys(&input_tys, sig.output, sig.is_variadic, layout_of, policy)
}

pub fn compute_fn_abi_from_tys<'gcx>(
    inputs: &[Ty<'gcx>],
    output: Ty<'gcx>,
    c_variadic: bool,
    mut layout_of: impl FnMut(Ty<'gcx>) -> Option<TypeLayout>,
    policy: AbiPolicy,
) -> FnAbi<'gcx> {
    let ret_layout = layout_of(output);
    let ret = ArgAbi {
        ty: output,
        mode: classify_return_mode(output, ret_layout, policy),
    };

    let mut args = Vec::with_capacity(inputs.len());
    for ty in inputs {
        let layout = layout_of(*ty);
        args.push(ArgAbi {
            ty: *ty,
            mode: classify_arg_mode(*ty, layout, policy),
        });
    }

    FnAbi {
        ret,
        args,
        c_variadic,
    }
}

fn classify_arg_mode(ty: Ty<'_>, layout: Option<TypeLayout>, policy: AbiPolicy) -> PassMode {
    let Some(layout) = layout else {
        return PassMode::Ignore;
    };

    if policy.enable_indirect_args
        && layout.size >= policy.indirect_arg_threshold_bytes
        && should_consider_indirect_argument(ty)
    {
        return PassMode::Indirect {
            align: layout.align,
            size: layout.size,
        };
    }

    PassMode::Direct
}

fn classify_return_mode(ty: Ty<'_>, layout: Option<TypeLayout>, policy: AbiPolicy) -> PassMode {
    let Some(layout) = layout else {
        return PassMode::Ignore;
    };

    if policy.enable_indirect_returns
        && layout.size >= policy.indirect_return_threshold_bytes
        && should_consider_indirect_return(ty)
    {
        return PassMode::Indirect {
            align: layout.align,
            size: layout.size,
        };
    }

    PassMode::Direct
}

fn should_consider_indirect_return(ty: Ty<'_>) -> bool {
    !matches!(
        ty.kind(),
        TyKind::Bool
            | TyKind::Rune
            | TyKind::Int(_)
            | TyKind::UInt(_)
            | TyKind::Float(_)
            | TyKind::Pointer(..)
            | TyKind::Reference(..)
            | TyKind::FnPointer { .. }
    )
}

fn should_consider_indirect_argument(ty: Ty<'_>) -> bool {
    should_consider_indirect_return(ty)
}
