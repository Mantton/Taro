//! Entry wrapper for `func main() -> Result[(), E]`.
//!
//! The program's entry becomes a compiler-generated function with the same
//! `async`-ness as `main`, equivalent to
//!
//! ```taro
//! func main$result_entry() -> int32 {
//!     match main() {            // `await main()` for an async `main`
//!         case .ok(_) => 0
//!         case .err(error) => std::runtime::reportMainError(error)
//!     }
//! }
//! ```
//!
//! so the status reaches the native entry shim as an ordinary `int32` result.
//! `main` and its `defer` blocks have finished before the error is reported,
//! and an async `main` is awaited inside the root task, so the error value
//! stays in GC-traced frames the whole time.
use crate::{
    compile::{
        context::GlobalContext,
        entry::{MainErrorConversion, ResultEntry},
    },
    hir::{DefinitionID, NodeID, StdItem},
    sema::models::{
        ClosureKind, FunctionPointerEffects, GenericArgument, GenericArguments, Generics,
        LabeledFunctionSignature, SyntheticDefinition, SyntheticDefinitionKind, Ty, TyKind,
    },
    thir::{
        Arm, ArmId, Block, BlockId, Constant, ConstantKind, Expr, ExprId, ExprKind,
        FieldIndex, FieldPattern, Pattern, PatternKind, ThirFunction,
    },
};
use index_vec::IndexVec;
use rustc_hash::FxHashMap;

/// Build the wrapper around a `Result`-returning `main`.
pub(crate) fn synthesize_entry<'ctx>(
    gcx: GlobalContext<'ctx>,
    main: DefinitionID,
    is_async: bool,
    entry: ResultEntry<'ctx>,
) -> ThirFunction<'ctx> {
    let span = gcx.definition_ident(main).span;
    let status_ty = gcx.types.int32;
    let id = register_definition(gcx, main, is_async, status_ty, span);

    let mut exprs: IndexVec<ExprId, Expr<'ctx>> = IndexVec::new();
    let mut push = |kind: ExprKind<'ctx>, ty: Ty<'ctx>| exprs.push(Expr { kind, ty, span });

    // `main()`, awaited when `main` is async.
    let callee = push(
        ExprKind::Zst {
            id: main,
            generic_args: Some(GenericArguments::empty()),
        },
        gcx.get_type(main),
    );
    let mut scrutinee = push(
        ExprKind::Call {
            callee,
            args: vec![],
            argument_evaluation_order: None,
            is_async,
        },
        entry.result_ty,
    );
    if is_async {
        scrutinee = push(ExprKind::Await { future: scrutinee }, entry.result_ty);
    }

    let TyKind::Adt(result_def, result_args) = entry.result_ty.kind() else {
        unreachable!("validated entry result is a Result");
    };
    let error_ty = result_args
        .get(1)
        .copied()
        .and_then(GenericArgument::ty)
        .expect("Result[T, E] error type");
    let enum_def = gcx.get_enum_definition(result_def.id);
    let variant = |item: StdItem| {
        let def_id = gcx.std_item_def(item).expect("Result variant language item");
        *enum_def
            .variants
            .iter()
            .find(|variant| variant.def_id == def_id)
            .expect("Result variant in its enum definition")
    };
    let ok_variant = variant(StdItem::ResultOkVariant);
    let err_variant = variant(StdItem::ResultErrVariant);
    // `case .ok(_) => 0`
    let ok_pattern = Pattern {
        ty: entry.result_ty,
        span,
        kind: PatternKind::Variant {
            definition: enum_def.adt_def,
            variant: ok_variant,
            subpatterns: vec![FieldPattern {
                index: FieldIndex::from_usize(0),
                pattern: Pattern {
                    ty: gcx.types.void,
                    span,
                    kind: PatternKind::Wild,
                },
            }],
        },
    };
    let success = push(
        ExprKind::Literal(Constant {
            ty: status_ty,
            value: ConstantKind::Integer(0),
        }),
        status_ty,
    );

    // `case .err(error) => reportMainError(error)`
    let error_local = NodeID::from_raw(u32::MAX);
    let err_pattern = Pattern {
        ty: entry.result_ty,
        span,
        kind: PatternKind::Variant {
            definition: enum_def.adt_def,
            variant: err_variant,
            subpatterns: vec![FieldPattern {
                index: FieldIndex::from_usize(0),
                pattern: Pattern {
                    ty: error_ty,
                    span,
                    kind: PatternKind::Binding {
                        name: gcx.intern_symbol("error"),
                        local: error_local,
                        ty: error_ty,
                    },
                },
            }],
        },
    };
    let error_value = push(ExprKind::Local(error_local), error_ty);
    let displayed = match entry.conversion {
        MainErrorConversion::Identity => error_value,
        MainErrorConversion::BoxExistential { interfaces } => push(
            ExprKind::BoxExistential {
                value: error_value,
                interfaces,
            },
            entry.display_ty,
        ),
        MainErrorConversion::ExistentialUpcast => push(
            ExprKind::ExistentialUpcast {
                value: error_value,
                to: entry.display_ty,
            },
            entry.display_ty,
        ),
    };
    let reporter = push(
        ExprKind::Zst {
            id: entry.reporter,
            generic_args: Some(GenericArguments::empty()),
        },
        gcx.get_type(entry.reporter),
    );
    let failure = push(
        ExprKind::Call {
            callee: reporter,
            args: vec![displayed],
            argument_evaluation_order: None,
            is_async: false,
        },
        status_ty,
    );

    let mut arms = IndexVec::new();
    let ok_arm: ArmId = arms.push(Arm {
        pattern: Box::new(ok_pattern),
        guard: None,
        body: success,
        span,
    });
    let err_arm: ArmId = arms.push(Arm {
        pattern: Box::new(err_pattern),
        guard: None,
        body: failure,
        span,
    });
    let status = push(
        ExprKind::Match {
            scrutinee,
            arms: vec![ok_arm, err_arm],
            binding_condition: false,
        },
        status_ty,
    );

    let mut blocks = IndexVec::new();
    let body: BlockId = blocks.push(Block {
        id: BlockId::from_raw(0),
        stmts: vec![],
        expr: Some(status),
    });

    ThirFunction {
        id,
        body: Some(body),
        constructor_self: None,
        span,
        params: vec![],
        stmts: IndexVec::new(),
        blocks,
        exprs,
        arms,
        match_reports: FxHashMap::default(),
        is_async,
    }
}

fn register_definition<'ctx>(
    gcx: GlobalContext<'ctx>,
    main: DefinitionID,
    is_async: bool,
    status_ty: Ty<'ctx>,
    span: crate::span::Span,
) -> DefinitionID {
    let id = gcx.allocate_synthetic_id(main.package());
    let signature = LabeledFunctionSignature {
        inputs: vec![],
        output: status_ty,
        is_variadic: false,
        abi: None,
    };
    let signature_ref = gcx.store.arenas.function_signatures.alloc(signature.clone());
    let main_name = gcx.definition_symbol_or_fallback(main);
    gcx.register_synthetic_definition(
        id,
        SyntheticDefinition {
            kind: SyntheticDefinitionKind::Ordinary,
            name: gcx.intern_symbol(&format!("{}$result_entry", gcx.symbol_text(main_name))),
            generics: gcx.store.arenas.generics.alloc(Generics {
                parameters: vec![],
                has_self: false,
                parent: None,
                parent_count: 0,
            }),
            signature: signature_ref,
            span,
        },
    );
    if is_async {
        gcx.cache_async_body_output(id, status_ty);
    }
    let ty = Ty::new(
        TyKind::FnPointer {
            inputs: gcx.store.interners.intern_ty_list(vec![]),
            output: status_ty,
            effects: FunctionPointerEffects {
                kind: if is_async {
                    ClosureKind::AsyncFn
                } else {
                    ClosureKind::Fn
                },
                is_unsafe: false,
                abi: None,
            },
        },
        gcx,
    );
    gcx.cache_signature(id, signature);
    gcx.cache_type(id, ty);
    id
}
