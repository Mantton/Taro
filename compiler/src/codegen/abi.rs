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

#[cfg(test)]
mod tests {
    use super::{AbiPolicy, PassMode, TypeLayout, compute_fn_abi_from_tys};
    use crate::{
        PackageIndex,
        compile::{
            config::{BuildProfile, Config, DebugOptions, PackageKind, StdMode},
            context::{CompilerArenas, CompilerContext, CompilerStore, Gcx},
        },
        diagnostics::DiagCtx,
        sema::models::{Ty, TyKind},
    };
    use rustc_hash::FxHashMap;
    use std::{path::PathBuf, rc::Rc};

    fn with_test_gcx<R>(f: impl for<'ctx> FnOnce(Gcx<'ctx>) -> R) -> R {
        let root = std::env::temp_dir().join(format!(
            "taro-abi-test-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("time")
                .as_nanos()
        ));
        std::fs::create_dir_all(&root).expect("temp dir");

        let dcx = Rc::new(DiagCtx::new(PathBuf::from(".")));
        let arenas = CompilerArenas::new();
        let store = CompilerStore::new(&arenas, root, &dcx, None, BuildProfile::Debug)
            .unwrap_or_else(|_| panic!("store"));
        let icx = CompilerContext::new(dcx, store);
        let config = icx.store.arenas.configs.alloc(Config {
            name: "abi-test".into(),
            identifier: "abi-test".into(),
            src: PathBuf::from("abi-test.tr"),
            dependencies: FxHashMap::default(),
            index: PackageIndex::new(1),
            kind: PackageKind::Library,
            executable_out: None,
            no_std_prelude: true,
            is_script: true,
            profile: BuildProfile::Debug,
            overflow_checks: false,
            debug: DebugOptions {
                dump_mir: false,
                dump_llvm: false,
                timings: false,
                debug_info: Default::default(),
            },
            test_mode: false,
            std_mode: StdMode::BootstrapStd,
            is_std_provider: false,
        });

        f(Gcx::new(&icx, config))
    }

    fn aggregate_ty<'gcx>(gcx: Gcx<'gcx>) -> Ty<'gcx> {
        let fields = gcx
            .store
            .interners
            .intern_ty_list(vec![gcx.types.int64, gcx.types.int64]);
        Ty::new(TyKind::Tuple(fields), gcx)
    }

    #[test]
    fn large_aggregates_use_indirect_modes_when_enabled() {
        with_test_gcx(|gcx| {
            let aggregate = aggregate_ty(gcx);
            let policy = AbiPolicy {
                enable_indirect_returns: true,
                indirect_return_threshold_bytes: 16,
                enable_indirect_args: true,
                indirect_arg_threshold_bytes: 16,
            };
            let abi = compute_fn_abi_from_tys(
                &[aggregate],
                aggregate,
                false,
                |_| Some(TypeLayout { size: 16, align: 8 }),
                policy,
            );

            assert_eq!(abi.ret.mode, PassMode::Indirect { align: 8, size: 16 });
            assert_eq!(abi.args[0].mode, PassMode::Indirect { align: 8, size: 16 });
        });
    }

    #[test]
    fn primitive_scalars_stay_direct_above_indirect_threshold() {
        with_test_gcx(|gcx| {
            let policy = AbiPolicy {
                enable_indirect_returns: true,
                indirect_return_threshold_bytes: 1,
                enable_indirect_args: true,
                indirect_arg_threshold_bytes: 1,
            };
            let abi = compute_fn_abi_from_tys(
                &[gcx.types.int64],
                gcx.types.int64,
                false,
                |_| Some(TypeLayout { size: 8, align: 8 }),
                policy,
            );

            assert_eq!(abi.ret.mode, PassMode::Direct);
            assert_eq!(abi.args[0].mode, PassMode::Direct);
        });
    }

    #[test]
    fn unlowerable_types_are_ignored_in_abi() {
        with_test_gcx(|gcx| {
            let policy = AbiPolicy {
                enable_indirect_returns: true,
                indirect_return_threshold_bytes: 0,
                enable_indirect_args: true,
                indirect_arg_threshold_bytes: 0,
            };
            let abi =
                compute_fn_abi_from_tys(&[gcx.types.void], gcx.types.void, false, |_| None, policy);

            assert_eq!(abi.ret.mode, PassMode::Ignore);
            assert_eq!(abi.args[0].mode, PassMode::Ignore);
        });
    }
}
