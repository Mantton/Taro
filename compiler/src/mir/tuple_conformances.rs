//! Built-in structural conformances (`PartialEq`, `Hashable`, `PartialOrd`,
//! `Ord`, `Default`, `Debug`) for arbitrary tuple types `(T0, T1, ...)`.
//!
//! Like `copy_clone`, one generic synthetic declaration per interface is shared
//! and materialized into concrete MIR per tuple instantiation so layouts never
//! collide across arities or element types.
use crate::{
    compile::context::Gcx,
    error::{CompileResult, ReportedError},
    hir::{DefinitionID, StdItem},
    mir::{
        AggregateKind, BasicBlockData, BasicBlockId, Body, CallUnwindAction, Constant,
        ConstantKind, LocalDecl, LocalId, LocalKind, MirPhase, Operand, Place, PlaceElem, Rvalue,
        Statement, StatementKind, Terminator, TerminatorKind,
    },
    sema::{
        models::{
            AdtDef, GenericArgument, GenericArguments, GenericParameter,
            GenericParameterDefinition, GenericParameterDefinitionKind, Generics, GoalResult,
            InterfaceGoal, LabeledFunctionParameter, LabeledFunctionSignature, SelectionMode,
            SyntheticDefinition, SyntheticDefinitionKind, Ty, TyKind,
        },
        tycheck::utils::{
            instantiate::instantiate_ty_with_args, normalize_aliases,
            normalize_post_monomorphization, unresolved::storage_needs_substitution,
        },
    },
    span::Span,
    specialize::Instance,
    thir::{FieldIndex, VariantIndex},
};
use index_vec::IndexVec;

/// Interfaces for which tuple types receive built-in structural conformances.
pub(crate) const CONFORMANCE_ITEMS: &[StdItem] = &[
    StdItem::PartialEq,
    StdItem::Equatable,
    StdItem::Hashable,
    StdItem::PartialOrd,
    StdItem::Ord,
    StdItem::Default,
    StdItem::Debug,
];

/// Subset of `CONFORMANCE_ITEMS` that materialize a synthetic method body.
pub(crate) fn has_synthetic_method(item: StdItem) -> bool {
    matches!(
        item,
        StdItem::PartialEq
            | StdItem::Hashable
            | StdItem::PartialOrd
            | StdItem::Ord
            | StdItem::Default
            | StdItem::Debug
    )
}

pub(crate) fn is_rhs_parameterized(item: StdItem) -> bool {
    matches!(
        item,
        StdItem::PartialEq | StdItem::Equatable | StdItem::PartialOrd
    )
}

pub(crate) fn primary_method_name(item: StdItem) -> Option<&'static str> {
    Some(match item {
        StdItem::PartialEq => "eq",
        StdItem::Hashable => "hash",
        StdItem::PartialOrd => "partialCmp",
        StdItem::Ord => "cmp",
        StdItem::Default => "default",
        StdItem::Debug => "debug",
        _ => return None,
    })
}

fn synthetic_symbol_name(item: StdItem) -> &'static str {
    match item {
        StdItem::PartialEq => "$tupleEq",
        StdItem::Hashable => "$tupleHash",
        StdItem::PartialOrd => "$tuplePartialCmp",
        StdItem::Ord => "$tupleCmp",
        StdItem::Default => "$tupleDefault",
        StdItem::Debug => "$tupleDebug",
        _ => unreachable!("unsupported tuple conformance item"),
    }
}

fn find_interface_method(gcx: Gcx<'_>, item: StdItem, name: &str) -> Option<DefinitionID> {
    let interface_id = gcx.std_item_def(item)?;
    let requirements = gcx.get_interface_requirements(interface_id)?;
    requirements
        .methods
        .iter()
        .find(|method| gcx.symbol_eq(method.name, name))
        .map(|method| method.id)
}

pub(crate) fn declaration(gcx: Gcx<'_>, item: StdItem, span: Span) -> Option<DefinitionID> {
    if !has_synthetic_method(item) {
        return None;
    }
    let kind = SyntheticDefinitionKind::TupleConformance(item);
    if let Some(id) =
        gcx.store
            .synthetic_definitions
            .borrow()
            .iter()
            .find_map(|(id, definition)| {
                (id.package() == gcx.package_index() && definition.kind == kind).then_some(*id)
            })
    {
        return Some(id);
    }

    let method_name = primary_method_name(item)?;
    let req_method_id = find_interface_method(gcx, item, method_name)?;
    let req_sig = gcx.get_signature(req_method_id);

    let id = gcx.allocate_synthetic_id(gcx.package_index());
    let t_param_id = gcx.allocate_synthetic_id(gcx.package_index());
    let t_name = gcx.intern_symbol("T");
    let t_ty = Ty::new(
        TyKind::Parameter(GenericParameter {
            index: 0,
            name: t_name,
        }),
        gcx,
    );

    let mut params = vec![GenericParameterDefinition {
        is_anonymous: false,
        name: t_name,
        id: t_param_id,
        index: 0,
        kind: GenericParameterDefinitionKind::Type { default: None },
    }];

    let (inputs, output) = match item {
        StdItem::PartialEq => (
            vec![
                param(gcx, "self", None, t_ty),
                param(gcx, "other", None, t_ty),
            ],
            gcx.types.bool,
        ),
        StdItem::Hashable => {
            let h_param_id = gcx.allocate_synthetic_id(gcx.package_index());
            let h_name = gcx.intern_symbol("H");
            let h_ty = Ty::new(
                TyKind::Parameter(GenericParameter {
                    index: 1,
                    name: h_name,
                }),
                gcx,
            );
            params.push(GenericParameterDefinition {
                is_anonymous: false,
                name: h_name,
                id: h_param_id,
                index: 1,
                kind: GenericParameterDefinitionKind::Type { default: None },
            });
            let hasher_label = req_sig.inputs.get(1).and_then(|input| input.label);
            (
                vec![
                    param(gcx, "self", None, t_ty),
                    param(gcx, "hasher", hasher_label, h_ty),
                ],
                gcx.types.void,
            )
        }
        StdItem::PartialOrd | StdItem::Ord => (
            vec![
                param(gcx, "self", None, t_ty),
                param(gcx, "other", None, t_ty),
            ],
            req_sig.output,
        ),
        StdItem::Default => (vec![], t_ty),
        StdItem::Debug => {
            let into_ty = req_sig.inputs.get(1)?.ty;
            let into_label = req_sig.inputs.get(1).and_then(|input| input.label);
            (
                vec![
                    param(gcx, "self", None, t_ty),
                    param(gcx, "into", into_label, into_ty),
                ],
                gcx.types.void,
            )
        }
        _ => return None,
    };

    let generics = gcx.store.arenas.generics.alloc(Generics {
        parameters: params,
        has_self: false,
        parent: None,
        parent_count: 0,
    });
    let signature = gcx
        .store
        .arenas
        .function_signatures
        .alloc(LabeledFunctionSignature {
            inputs,
            output,
            is_variadic: false,
            abi: None,
        });

    gcx.register_synthetic_definition(
        id,
        SyntheticDefinition {
            kind,
            name: gcx.intern_symbol(synthetic_symbol_name(item)),
            generics,
            signature,
            span,
        },
    );
    gcx.cache_type(id, Ty::from_labeled_signature(gcx, signature));
    Some(id)
}

fn param<'ctx>(
    gcx: Gcx<'ctx>,
    name: &str,
    label: Option<crate::span::Symbol>,
    ty: Ty<'ctx>,
) -> LabeledFunctionParameter<'ctx> {
    LabeledFunctionParameter {
        name: gcx.intern_symbol(name),
        label,
        is_lazy: false,
        default_provider: None,
        ty,
    }
}

pub fn validate_declaration<'ctx>(
    gcx: Gcx<'ctx>,
    definition: &SyntheticDefinition<'ctx>,
) -> Result<(), &'static str> {
    let SyntheticDefinitionKind::TupleConformance(item) = definition.kind else {
        return Ok(());
    };
    if !has_synthetic_method(item) {
        return Err("unsupported tuple conformance synthetic definition");
    }
    let generics = definition.generics;
    let expected_generics = if item == StdItem::Hashable { 2 } else { 1 };
    if generics.parameters.len() != expected_generics
        || generics.has_self
        || generics.parent.is_some()
        || generics.parent_count != 0
    {
        return Err("builtin tuple conformance metadata has invalid generics");
    }
    for (idx, parameter) in generics.parameters.iter().enumerate() {
        if parameter.index != idx
            || !matches!(
                &parameter.kind,
                GenericParameterDefinitionKind::Type { default: None }
            )
        {
            return Err("builtin tuple conformance metadata has invalid generic parameters");
        }
    }
    let signature = definition.signature;
    if signature.abi.is_some() || signature.is_variadic {
        return Err("builtin tuple conformance metadata has invalid ABI");
    }
    let t_param = &generics.parameters[0];
    let is_t = |ty: Ty<'_>| {
        matches!(ty.kind(), TyKind::Parameter(formal) if formal.index == 0 && formal.name == t_param.name)
    };
    match item {
        StdItem::PartialEq => {
            if signature.inputs.len() != 2
                || !is_t(signature.inputs[0].ty)
                || !is_t(signature.inputs[1].ty)
                || signature.output != gcx.types.bool
            {
                return Err("builtin tuple PartialEq metadata has invalid signature");
            }
        }
        StdItem::Hashable => {
            let h_param = &generics.parameters[1];
            let is_h = |ty: Ty<'_>| {
                matches!(ty.kind(), TyKind::Parameter(formal) if formal.index == 1 && formal.name == h_param.name)
            };
            if signature.inputs.len() != 2
                || !is_t(signature.inputs[0].ty)
                || !is_h(signature.inputs[1].ty)
                || signature.output != gcx.types.void
            {
                return Err("builtin tuple Hashable metadata has invalid signature");
            }
        }
        StdItem::PartialOrd | StdItem::Ord => {
            if signature.inputs.len() != 2
                || !is_t(signature.inputs[0].ty)
                || !is_t(signature.inputs[1].ty)
            {
                return Err("builtin tuple ordering metadata has invalid signature");
            }
        }
        StdItem::Default => {
            if !signature.inputs.is_empty() || !is_t(signature.output) {
                return Err("builtin tuple Default metadata has invalid signature");
            }
        }
        StdItem::Debug => {
            if signature.inputs.len() != 2
                || !is_t(signature.inputs[0].ty)
                || signature.output != gcx.types.void
            {
                return Err("builtin tuple Debug metadata has invalid signature");
            }
        }
        _ => return Err("unsupported tuple conformance synthetic definition"),
    }
    Ok(())
}

pub fn build_body<'ctx>(gcx: Gcx<'ctx>, instance: Instance<'ctx>) -> CompileResult<Body<'ctx>> {
    let owner = instance.def_id();
    let definition = gcx
        .store
        .synthetic_definitions
        .borrow()
        .get(&owner)
        .cloned();
    let Some(definition) = definition else {
        return Err(ReportedError);
    };
    let span = definition.span;
    let error = |message: &str| {
        gcx.dcx().emit_error(message.into(), Some(span));
        ReportedError
    };
    validate_declaration(gcx, &definition).map_err(error)?;
    let SyntheticDefinitionKind::TupleConformance(item) = definition.kind else {
        return Err(error("incorrect tuple conformance definition kind"));
    };

    let (tuple_ty, hasher_ty) = match item {
        StdItem::Hashable => {
            let [GenericArgument::Type(ty), GenericArgument::Type(hasher)] = &instance.args[..]
            else {
                return Err(error(
                    "builtin tuple Hashable requires tuple and hasher type arguments",
                ));
            };
            (
                normalize_post_monomorphization(gcx, *ty),
                Some(normalize_post_monomorphization(gcx, *hasher)),
            )
        }
        _ => {
            let [GenericArgument::Type(ty)] = &instance.args[..] else {
                return Err(error(
                    "builtin tuple conformance requires exactly one type argument",
                ));
            };
            (normalize_post_monomorphization(gcx, *ty), None)
        }
    };

    if storage_needs_substitution(gcx, tuple_ty)
        || hasher_ty.is_some_and(|h| storage_needs_substitution(gcx, h))
    {
        return Err(error("builtin tuple conformance requires concrete types"));
    }
    let TyKind::Tuple(fields) = normalize_aliases(gcx, tuple_ty).kind() else {
        return Err(error("builtin tuple conformance requires a tuple type"));
    };
    let fields = fields.to_vec();

    // Verify every element satisfies the required interface at codegen time.
    let interface_id = gcx
        .std_item_def(item)
        .ok_or_else(|| error("missing interface for builtin tuple conformance"))?;
    for &field in &fields {
        let interface_args = if is_rhs_parameterized(item) {
            gcx.store
                .interners
                .intern_generic_args(vec![GenericArgument::Type(field)])
        } else {
            GenericArguments::empty()
        };
        let goal = InterfaceGoal {
            interface_id,
            self_ty: field,
            interface_args,
            bindings: &[],
            param_env: &[],
        };
        if gcx.prove_interface_goal(goal, SelectionMode::Codegen) != GoalResult::Proven {
            return Err(error(
                "builtin tuple conformance requires every element to satisfy the interface",
            ));
        }
    }

    let mut body = match item {
        StdItem::PartialEq => build_partial_eq(gcx, owner, tuple_ty, &fields, span)?,
        StdItem::Hashable => {
            build_hash(gcx, owner, tuple_ty, hasher_ty.unwrap(), &fields, span)?
        }
        StdItem::PartialOrd => {
            build_partial_ord(gcx, owner, tuple_ty, definition.signature.output, &fields, span)?
        }
        StdItem::Ord => build_ord(gcx, owner, tuple_ty, definition.signature.output, &fields, span)?,
        StdItem::Default => build_default(gcx, owner, tuple_ty, &fields, span)?,
        StdItem::Debug => build_debug(
            gcx,
            owner,
            tuple_ty,
            definition.signature.inputs[1].ty,
            &fields,
            span,
        )?,
        _ => return Err(error("unsupported tuple conformance item")),
    };

    crate::mir::optimize::run_passes(
        gcx,
        &mut body,
        &mut [
            Box::new(crate::mir::optimize::passes::PruneUnreachable),
            Box::new(crate::mir::optimize::passes::SimplifyCfg),
        ],
    )?;
    Ok(body)
}

fn new_body<'ctx>(
    owner: DefinitionID,
    return_ty: Ty<'ctx>,
    params: &[(Ty<'ctx>, Option<crate::span::Symbol>)],
    note: &str,
    span: Span,
) -> (Body<'ctx>, LocalId, Vec<LocalId>, BasicBlockId, BasicBlockId) {
    let mut locals = IndexVec::new();
    let return_local = locals.push(LocalDecl {
        ty: return_ty,
        kind: LocalKind::Return,
        mutable: true,
        name: None,
        span,
    });
    let mut param_locals = Vec::with_capacity(params.len());
    for &(ty, name) in params {
        param_locals.push(locals.push(LocalDecl {
            ty,
            kind: LocalKind::Param,
            mutable: false,
            name,
            span,
        }));
    }
    let mut blocks = IndexVec::new();
    let start_block = blocks.push(BasicBlockData {
        note: Some(note.into()),
        statements: vec![],
        terminator: None,
    });
    let unwind = blocks.push(BasicBlockData {
        note: None,
        statements: vec![],
        terminator: Some(Terminator {
            kind: TerminatorKind::ResumeUnwind,
            span,
        }),
    });
    let body = Body {
        escape_locals: Vec::new(),
        owner,
        source_scopes: Body::initial_source_scopes(owner),
        locals,
        basic_blocks: blocks,
        return_local,
        start_block,
        phase: MirPhase::CfgClean,
        is_async: false,
        generator_element_ty: None,
    };
    (body, return_local, param_locals, start_block, unwind)
}

fn temp<'ctx>(body: &mut Body<'ctx>, ty: Ty<'ctx>, span: Span) -> LocalId {
    body.locals.push(LocalDecl {
        ty,
        kind: LocalKind::Temp,
        mutable: true,
        name: None,
        span,
    })
}

fn block(body: &mut Body<'_>, note: &str) -> BasicBlockId {
    body.basic_blocks.push(BasicBlockData {
        note: Some(note.into()),
        statements: vec![],
        terminator: None,
    })
}

fn field_place<'ctx>(local: LocalId, index: usize, field_ty: Ty<'ctx>) -> Place<'ctx> {
    Place {
        local,
        projection: vec![PlaceElem::Field(FieldIndex::from_usize(index), field_ty)],
    }
}

fn fn_operand<'ctx>(
    gcx: Gcx<'ctx>,
    def_id: DefinitionID,
    args: GenericArguments<'ctx>,
) -> Operand<'ctx> {
    let raw_sig = Ty::from_labeled_signature(gcx, gcx.get_signature(def_id));
    let signature = if args.is_empty() {
        raw_sig
    } else {
        instantiate_ty_with_args(gcx, raw_sig, args)
    };
    Operand::Constant(Constant {
        ty: signature,
        value: ConstantKind::Function(def_id, args, signature),
    })
}

fn build_partial_eq<'ctx>(
    gcx: Gcx<'ctx>,
    owner: DefinitionID,
    tuple_ty: Ty<'ctx>,
    fields: &[Ty<'ctx>],
    span: Span,
) -> CompileResult<Body<'ctx>> {
    let eq_method = find_interface_method(gcx, StdItem::PartialEq, "eq").ok_or_else(|| {
        gcx.dcx()
            .emit_error("missing PartialEq::eq method".into(), Some(span));
        ReportedError
    })?;
    let (mut body, return_local, params, start_block, unwind) = new_body(
        owner,
        gcx.types.bool,
        &[
            (tuple_ty, Some(gcx.intern_symbol("self"))),
            (tuple_ty, Some(gcx.intern_symbol("other"))),
        ],
        "begin tuple PartialEq",
        span,
    );
    let lhs_param = params[0];
    let rhs_param = params[1];

    if fields.is_empty() {
        body.basic_blocks[start_block].statements.push(Statement {
            span,
            kind: StatementKind::Assign(
                Place::from_local(return_local),
                Rvalue::Use(Operand::Constant(Constant {
                    ty: gcx.types.bool,
                    value: ConstantKind::Bool(true),
                })),
            ),
        });
        body.basic_blocks[start_block].terminator = Some(Terminator {
            span,
            kind: TerminatorKind::Return,
        });
        return Ok(body);
    }

    let return_false = block(&mut body, "tuple eq false");
    body.basic_blocks[return_false].statements.push(Statement {
        span,
        kind: StatementKind::Assign(
            Place::from_local(return_local),
            Rvalue::Use(Operand::Constant(Constant {
                ty: gcx.types.bool,
                value: ConstantKind::Bool(false),
            })),
        ),
    });
    body.basic_blocks[return_false].terminator = Some(Terminator {
        span,
        kind: TerminatorKind::Return,
    });

    let return_ok = block(&mut body, "tuple eq return");
    body.basic_blocks[return_ok].terminator = Some(Terminator {
        span,
        kind: TerminatorKind::Return,
    });

    let mut current = start_block;
    let last_index = fields.len() - 1;
    for (index, &field_ty) in fields.iter().enumerate() {
        let args = gcx.store.interners.intern_generic_args(vec![
            GenericArgument::Type(field_ty),
            GenericArgument::Type(field_ty),
        ]);
        let callee = fn_operand(gcx, eq_method, args);
        let lhs_field = field_place(lhs_param, index, field_ty);
        let rhs_field = field_place(rhs_param, index, field_ty);

        if index == last_index {
            body.basic_blocks[current].terminator = Some(Terminator {
                span,
                kind: TerminatorKind::Call {
                    func: callee,
                    args: vec![Operand::Copy(lhs_field), Operand::Copy(rhs_field)],
                    destination: Place::from_local(return_local),
                    target: return_ok,
                    unwind: CallUnwindAction::Cleanup(unwind),
                },
            });
        } else {
            let eq_res = temp(&mut body, gcx.types.bool, span);
            let check = block(&mut body, "check tuple element eq");
            let next = block(&mut body, "next tuple element eq");
            body.basic_blocks[current].terminator = Some(Terminator {
                span,
                kind: TerminatorKind::Call {
                    func: callee,
                    args: vec![Operand::Copy(lhs_field), Operand::Copy(rhs_field)],
                    destination: Place::from_local(eq_res),
                    target: check,
                    unwind: CallUnwindAction::Cleanup(unwind),
                },
            });
            body.basic_blocks[check].terminator = Some(Terminator {
                span,
                kind: TerminatorKind::if_(Operand::Copy(Place::from_local(eq_res)), next, return_false),
            });
            current = next;
        }
    }
    Ok(body)
}

fn build_hash<'ctx>(
    gcx: Gcx<'ctx>,
    owner: DefinitionID,
    tuple_ty: Ty<'ctx>,
    hasher_ty: Ty<'ctx>,
    fields: &[Ty<'ctx>],
    span: Span,
) -> CompileResult<Body<'ctx>> {
    let hash_method = find_interface_method(gcx, StdItem::Hashable, "hash").ok_or_else(|| {
        gcx.dcx()
            .emit_error("missing Hashable::hash method".into(), Some(span));
        ReportedError
    })?;
    let (mut body, return_local, params, start_block, unwind) = new_body(
        owner,
        gcx.types.void,
        &[
            (tuple_ty, Some(gcx.intern_symbol("self"))),
            (hasher_ty, Some(gcx.intern_symbol("hasher"))),
        ],
        "begin tuple Hashable",
        span,
    );
    let self_param = params[0];
    let hasher_param = params[1];

    let mut current = start_block;
    for (index, &field_ty) in fields.iter().enumerate() {
        let args = gcx.store.interners.intern_generic_args(vec![
            GenericArgument::Type(field_ty),
            GenericArgument::Type(hasher_ty),
        ]);
        let callee = fn_operand(gcx, hash_method, args);
        let elem_unit = temp(&mut body, gcx.types.void, span);
        let next = block(&mut body, "next tuple element hash");
        body.basic_blocks[current].terminator = Some(Terminator {
            span,
            kind: TerminatorKind::Call {
                func: callee,
                args: vec![
                    Operand::Copy(field_place(self_param, index, field_ty)),
                    Operand::Copy(Place::from_local(hasher_param)),
                ],
                destination: Place::from_local(elem_unit),
                target: next,
                unwind: CallUnwindAction::Cleanup(unwind),
            },
        });
        current = next;
    }

    body.basic_blocks[current].statements.push(Statement {
        span,
        kind: StatementKind::Assign(
            Place::from_local(return_local),
            Rvalue::Use(Operand::Constant(Constant {
                ty: gcx.types.void,
                value: ConstantKind::Unit,
            })),
        ),
    });
    body.basic_blocks[current].terminator = Some(Terminator {
        span,
        kind: TerminatorKind::Return,
    });
    Ok(body)
}

fn ordering_equal_variant(gcx: Gcx<'_>, ordering_def: AdtDef, span: Span) -> CompileResult<usize> {
    gcx.get_enum_definition(ordering_def.id)
        .variants
        .iter()
        .position(|variant| gcx.symbol_eq(variant.name, "equal"))
        .ok_or_else(|| {
            gcx.dcx()
                .emit_error("missing Ordering::equal variant".into(), Some(span));
            ReportedError
        })
}

fn build_partial_ord<'ctx>(
    gcx: Gcx<'ctx>,
    owner: DefinitionID,
    tuple_ty: Ty<'ctx>,
    output_ty: Ty<'ctx>,
    fields: &[Ty<'ctx>],
    span: Span,
) -> CompileResult<Body<'ctx>> {
    let partial_cmp_method =
        find_interface_method(gcx, StdItem::PartialOrd, "partialCmp").ok_or_else(|| {
            gcx.dcx()
                .emit_error("missing PartialOrd::partialCmp method".into(), Some(span));
            ReportedError
        })?;
    let TyKind::Adt(optional_def, optional_args) = output_ty.kind() else {
        gcx.dcx().emit_error(
            "PartialOrd::partialCmp must return Optional[Ordering]".into(),
            Some(span),
        );
        return Err(ReportedError);
    };
    let some_def_id = gcx
        .std_item_def(StdItem::OptionalSomeVariant)
        .ok_or_else(|| {
            gcx.dcx()
                .emit_error("missing Optional::some std item".into(), Some(span));
            ReportedError
        })?;
    let optional_enum = gcx.get_enum_definition(optional_def.id);
    let some_index = optional_enum
        .variants
        .iter()
        .position(|variant| variant.def_id == some_def_id)
        .ok_or_else(|| {
            gcx.dcx()
                .emit_error("missing Optional::some variant".into(), Some(span));
            ReportedError
        })?;
    let some_name = optional_enum.variants[some_index].name;
    let Some(GenericArgument::Type(ordering_ty)) = optional_args.first().copied() else {
        gcx.dcx().emit_error(
            "Optional[Ordering] missing Ordering argument".into(),
            Some(span),
        );
        return Err(ReportedError);
    };
    let TyKind::Adt(ordering_def, _) = ordering_ty.kind() else {
        gcx.dcx()
            .emit_error("Ordering must be an enum ADT".into(), Some(span));
        return Err(ReportedError);
    };
    let equal_index = ordering_equal_variant(gcx, ordering_def, span)?;

    let (mut body, return_local, params, start_block, unwind) = new_body(
        owner,
        output_ty,
        &[
            (tuple_ty, Some(gcx.intern_symbol("self"))),
            (tuple_ty, Some(gcx.intern_symbol("other"))),
        ],
        "begin tuple PartialOrd",
        span,
    );
    let lhs_param = params[0];
    let rhs_param = params[1];

    if fields.is_empty() {
        let eq_ord = temp(&mut body, ordering_ty, span);
        body.basic_blocks[start_block].statements.push(Statement {
            span,
            kind: StatementKind::Assign(
                Place::from_local(eq_ord),
                Rvalue::Aggregate {
                    kind: AggregateKind::Adt {
                        def_id: ordering_def.id,
                        variant_index: Some(VariantIndex::from_usize(equal_index)),
                        generic_args: GenericArguments::empty(),
                    },
                    fields: IndexVec::new(),
                },
            ),
        });
        let some_payload = Place {
            local: return_local,
            projection: vec![
                PlaceElem::VariantDowncast {
                    name: some_name,
                    index: VariantIndex::from_usize(some_index),
                },
                PlaceElem::Field(FieldIndex::from_usize(0), ordering_ty),
            ],
        };
        body.basic_blocks[start_block].statements.push(Statement {
            span,
            kind: StatementKind::Assign(
                some_payload,
                Rvalue::Use(Operand::Copy(Place::from_local(eq_ord))),
            ),
        });
        body.basic_blocks[start_block].statements.push(Statement {
            span,
            kind: StatementKind::SetDiscriminant {
                place: Place::from_local(return_local),
                variant_index: VariantIndex::from_usize(some_index),
            },
        });
        body.basic_blocks[start_block].statements.push(Statement {
            span,
            kind: StatementKind::SetInitialized(return_local),
        });
        body.basic_blocks[start_block].terminator = Some(Terminator {
            span,
            kind: TerminatorKind::Return,
        });
        return Ok(body);
    }

    let return_ok = block(&mut body, "tuple partialCmp return");
    body.basic_blocks[return_ok].terminator = Some(Terminator {
        span,
        kind: TerminatorKind::Return,
    });

    let mut current = start_block;
    let last_index = fields.len() - 1;
    for (index, &field_ty) in fields.iter().enumerate() {
        let args = gcx.store.interners.intern_generic_args(vec![
            GenericArgument::Type(field_ty),
            GenericArgument::Type(field_ty),
        ]);
        let callee = fn_operand(gcx, partial_cmp_method, args);
        let lhs_field = field_place(lhs_param, index, field_ty);
        let rhs_field = field_place(rhs_param, index, field_ty);

        if index == last_index {
            body.basic_blocks[current].terminator = Some(Terminator {
                span,
                kind: TerminatorKind::Call {
                    func: callee,
                    args: vec![Operand::Copy(lhs_field), Operand::Copy(rhs_field)],
                    destination: Place::from_local(return_local),
                    target: return_ok,
                    unwind: CallUnwindAction::Cleanup(unwind),
                },
            });
        } else {
            let res_local = temp(&mut body, output_ty, span);
            let opt_discr = temp(&mut body, gcx.types.uint, span);
            let ord_discr = temp(&mut body, gcx.types.uint, span);

            let check_opt = block(&mut body, "check partialCmp optional");
            let check_ord = block(&mut body, "check partialCmp ordering");
            let short_circuit = block(&mut body, "short-circuit partialCmp");
            let next = block(&mut body, "next tuple element partialCmp");

            body.basic_blocks[current].terminator = Some(Terminator {
                span,
                kind: TerminatorKind::Call {
                    func: callee,
                    args: vec![Operand::Copy(lhs_field), Operand::Copy(rhs_field)],
                    destination: Place::from_local(res_local),
                    target: check_opt,
                    unwind: CallUnwindAction::Cleanup(unwind),
                },
            });

            body.basic_blocks[check_opt].statements.push(Statement {
                span,
                kind: StatementKind::Assign(
                    Place::from_local(opt_discr),
                    Rvalue::Discriminant {
                        place: Place::from_local(res_local),
                    },
                ),
            });
            body.basic_blocks[check_opt].terminator = Some(Terminator {
                span,
                kind: TerminatorKind::SwitchInt {
                    discr: Operand::Copy(Place::from_local(opt_discr)),
                    targets: vec![(some_index as u128, check_ord)],
                    otherwise: short_circuit,
                },
            });

            let payload_place = Place {
                local: res_local,
                projection: vec![
                    PlaceElem::VariantDowncast {
                        name: some_name,
                        index: VariantIndex::from_usize(some_index),
                    },
                    PlaceElem::Field(FieldIndex::from_usize(0), ordering_ty),
                ],
            };
            body.basic_blocks[check_ord].statements.push(Statement {
                span,
                kind: StatementKind::Assign(
                    Place::from_local(ord_discr),
                    Rvalue::Discriminant {
                        place: payload_place,
                    },
                ),
            });
            body.basic_blocks[check_ord].terminator = Some(Terminator {
                span,
                kind: TerminatorKind::SwitchInt {
                    discr: Operand::Copy(Place::from_local(ord_discr)),
                    targets: vec![(equal_index as u128, next)],
                    otherwise: short_circuit,
                },
            });

            body.basic_blocks[short_circuit].statements.push(Statement {
                span,
                kind: StatementKind::Assign(
                    Place::from_local(return_local),
                    Rvalue::Use(Operand::Copy(Place::from_local(res_local))),
                ),
            });
            body.basic_blocks[short_circuit].terminator = Some(Terminator {
                span,
                kind: TerminatorKind::Return,
            });

            current = next;
        }
    }
    Ok(body)
}

fn build_ord<'ctx>(
    gcx: Gcx<'ctx>,
    owner: DefinitionID,
    tuple_ty: Ty<'ctx>,
    ordering_ty: Ty<'ctx>,
    fields: &[Ty<'ctx>],
    span: Span,
) -> CompileResult<Body<'ctx>> {
    let cmp_method = find_interface_method(gcx, StdItem::Ord, "cmp").ok_or_else(|| {
        gcx.dcx()
            .emit_error("missing Ord::cmp method".into(), Some(span));
        ReportedError
    })?;
    let TyKind::Adt(ordering_def, _) = ordering_ty.kind() else {
        gcx.dcx()
            .emit_error("Ord::cmp must return Ordering".into(), Some(span));
        return Err(ReportedError);
    };
    let equal_index = ordering_equal_variant(gcx, ordering_def, span)?;

    let (mut body, return_local, params, start_block, unwind) = new_body(
        owner,
        ordering_ty,
        &[
            (tuple_ty, Some(gcx.intern_symbol("self"))),
            (tuple_ty, Some(gcx.intern_symbol("other"))),
        ],
        "begin tuple Ord",
        span,
    );
    let lhs_param = params[0];
    let rhs_param = params[1];

    if fields.is_empty() {
        body.basic_blocks[start_block].statements.push(Statement {
            span,
            kind: StatementKind::Assign(
                Place::from_local(return_local),
                Rvalue::Aggregate {
                    kind: AggregateKind::Adt {
                        def_id: ordering_def.id,
                        variant_index: Some(VariantIndex::from_usize(equal_index)),
                        generic_args: GenericArguments::empty(),
                    },
                    fields: IndexVec::new(),
                },
            ),
        });
        body.basic_blocks[start_block].terminator = Some(Terminator {
            span,
            kind: TerminatorKind::Return,
        });
        return Ok(body);
    }

    let return_ok = block(&mut body, "tuple cmp return");
    body.basic_blocks[return_ok].terminator = Some(Terminator {
        span,
        kind: TerminatorKind::Return,
    });

    let mut current = start_block;
    let last_index = fields.len() - 1;
    for (index, &field_ty) in fields.iter().enumerate() {
        let args = gcx
            .store
            .interners
            .intern_generic_args(vec![GenericArgument::Type(field_ty)]);
        let callee = fn_operand(gcx, cmp_method, args);
        let lhs_field = field_place(lhs_param, index, field_ty);
        let rhs_field = field_place(rhs_param, index, field_ty);

        if index == last_index {
            body.basic_blocks[current].terminator = Some(Terminator {
                span,
                kind: TerminatorKind::Call {
                    func: callee,
                    args: vec![Operand::Copy(lhs_field), Operand::Copy(rhs_field)],
                    destination: Place::from_local(return_local),
                    target: return_ok,
                    unwind: CallUnwindAction::Cleanup(unwind),
                },
            });
        } else {
            let res_local = temp(&mut body, ordering_ty, span);
            let ord_discr = temp(&mut body, gcx.types.uint, span);

            let check_ord = block(&mut body, "check tuple cmp ordering");
            let short_circuit = block(&mut body, "short-circuit tuple cmp");
            let next = block(&mut body, "next tuple element cmp");

            body.basic_blocks[current].terminator = Some(Terminator {
                span,
                kind: TerminatorKind::Call {
                    func: callee,
                    args: vec![Operand::Copy(lhs_field), Operand::Copy(rhs_field)],
                    destination: Place::from_local(res_local),
                    target: check_ord,
                    unwind: CallUnwindAction::Cleanup(unwind),
                },
            });

            body.basic_blocks[check_ord].statements.push(Statement {
                span,
                kind: StatementKind::Assign(
                    Place::from_local(ord_discr),
                    Rvalue::Discriminant {
                        place: Place::from_local(res_local),
                    },
                ),
            });
            body.basic_blocks[check_ord].terminator = Some(Terminator {
                span,
                kind: TerminatorKind::SwitchInt {
                    discr: Operand::Copy(Place::from_local(ord_discr)),
                    targets: vec![(equal_index as u128, next)],
                    otherwise: short_circuit,
                },
            });

            body.basic_blocks[short_circuit].statements.push(Statement {
                span,
                kind: StatementKind::Assign(
                    Place::from_local(return_local),
                    Rvalue::Use(Operand::Copy(Place::from_local(res_local))),
                ),
            });
            body.basic_blocks[short_circuit].terminator = Some(Terminator {
                span,
                kind: TerminatorKind::Return,
            });

            current = next;
        }
    }
    Ok(body)
}

fn build_default<'ctx>(
    gcx: Gcx<'ctx>,
    owner: DefinitionID,
    tuple_ty: Ty<'ctx>,
    fields: &[Ty<'ctx>],
    span: Span,
) -> CompileResult<Body<'ctx>> {
    let default_method = find_interface_method(gcx, StdItem::Default, "default").ok_or_else(|| {
        gcx.dcx()
            .emit_error("missing Default::default method".into(), Some(span));
        ReportedError
    })?;
    let (mut body, return_local, _, start_block, unwind) =
        new_body(owner, tuple_ty, &[], "begin tuple Default", span);

    if fields.is_empty() {
        body.basic_blocks[start_block].statements.push(Statement {
            span,
            kind: StatementKind::Assign(
                Place::from_local(return_local),
                Rvalue::Use(Operand::Constant(Constant {
                    ty: tuple_ty,
                    value: ConstantKind::Unit,
                })),
            ),
        });
        body.basic_blocks[start_block].terminator = Some(Terminator {
            span,
            kind: TerminatorKind::Return,
        });
        return Ok(body);
    }

    // Stage completed element defaults in rooted locals; move them into the
    // return tuple only in the final safepoint-free block.
    let mut current = start_block;
    let mut completed = Vec::with_capacity(fields.len());
    for &field_ty in fields {
        let result = temp(&mut body, field_ty, span);
        let after = block(&mut body, "next tuple default element");
        let args = gcx
            .store
            .interners
            .intern_generic_args(vec![GenericArgument::Type(field_ty)]);
        let callee = fn_operand(gcx, default_method, args);
        body.basic_blocks[current].terminator = Some(Terminator {
            span,
            kind: TerminatorKind::Call {
                func: callee,
                args: vec![],
                destination: Place::from_local(result),
                target: after,
                unwind: CallUnwindAction::Cleanup(unwind),
            },
        });
        completed.push((result, field_ty));
        current = after;
    }

    for (index, (local, field_ty)) in completed.into_iter().enumerate() {
        body.basic_blocks[current].statements.push(Statement {
            span,
            kind: StatementKind::Assign(
                field_place(return_local, index, field_ty),
                Rvalue::Use(Operand::Copy(Place::from_local(local))),
            ),
        });
    }
    body.basic_blocks[current].statements.push(Statement {
        span,
        kind: StatementKind::SetInitialized(return_local),
    });
    body.basic_blocks[current].terminator = Some(Terminator {
        span,
        kind: TerminatorKind::Return,
    });
    Ok(body)
}

fn build_debug<'ctx>(
    gcx: Gcx<'ctx>,
    owner: DefinitionID,
    tuple_ty: Ty<'ctx>,
    into_ty: Ty<'ctx>,
    fields: &[Ty<'ctx>],
    span: Span,
) -> CompileResult<Body<'ctx>> {
    let debug_method = find_interface_method(gcx, StdItem::Debug, "debug").ok_or_else(|| {
        gcx.dcx()
            .emit_error("missing Debug::debug method".into(), Some(span));
        ReportedError
    })?;
    let write_id =
        crate::mir::optimize::async_transform::find_std_function(gcx, "fmt", "__debug_write", span)?;

    let (mut body, return_local, params, start_block, unwind) = new_body(
        owner,
        gcx.types.void,
        &[
            (tuple_ty, Some(gcx.intern_symbol("self"))),
            (into_ty, Some(gcx.intern_symbol("into"))),
        ],
        "begin tuple Debug",
        span,
    );
    let self_param = params[0];
    let into_param = params[1];

    let mut current = start_block;
    let write_text = |body: &mut Body<'ctx>, current: &mut BasicBlockId, text: &str| {
        let callee = fn_operand(gcx, write_id, GenericArguments::empty());
        let unit = temp(body, gcx.types.void, span);
        let next = block(body, "after tuple debug text");
        body.basic_blocks[*current].terminator = Some(Terminator {
            span,
            kind: TerminatorKind::Call {
                func: callee,
                args: vec![
                    Operand::Copy(Place::from_local(into_param)),
                    Operand::Constant(Constant {
                        ty: gcx.types.string,
                        value: ConstantKind::String(gcx.intern_symbol(text)),
                    }),
                ],
                destination: Place::from_local(unit),
                target: next,
                unwind: CallUnwindAction::Cleanup(unwind),
            },
        });
        *current = next;
    };

    if fields.is_empty() {
        write_text(&mut body, &mut current, "()");
    } else {
        write_text(&mut body, &mut current, "(");
        for (index, &field_ty) in fields.iter().enumerate() {
            if index > 0 {
                write_text(&mut body, &mut current, ", ");
            }
            let args = gcx
                .store
                .interners
                .intern_generic_args(vec![GenericArgument::Type(field_ty)]);
            let callee = fn_operand(gcx, debug_method, args);
            let unit = temp(&mut body, gcx.types.void, span);
            let next = block(&mut body, "after tuple debug element");
            body.basic_blocks[current].terminator = Some(Terminator {
                span,
                kind: TerminatorKind::Call {
                    func: callee,
                    args: vec![
                        Operand::Copy(field_place(self_param, index, field_ty)),
                        Operand::Copy(Place::from_local(into_param)),
                    ],
                    destination: Place::from_local(unit),
                    target: next,
                    unwind: CallUnwindAction::Cleanup(unwind),
                },
            });
            current = next;
        }
        if fields.len() == 1 {
            write_text(&mut body, &mut current, ",)");
        } else {
            write_text(&mut body, &mut current, ")");
        }
    }

    body.basic_blocks[current].statements.push(Statement {
        span,
        kind: StatementKind::Assign(
            Place::from_local(return_local),
            Rvalue::Use(Operand::Constant(Constant {
                ty: gcx.types.void,
                value: ConstantKind::Unit,
            })),
        ),
    });
    body.basic_blocks[current].terminator = Some(Terminator {
        span,
        kind: TerminatorKind::Return,
    });
    Ok(body)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tuple_conformance_declarations_survive_metadata_roundtrip() {
        crate::test_support::analyze_script_built_mir_with_items(
            "interface PartialEq[Rhs = Self] {\nfunc eq(_ other: Rhs) -> bool\n}\n\
             interface Hasher {\nfunc finish() -> uint64\n}\n\
             interface Hashable: PartialEq {\nfunc hash[H: Hasher](into hasher: H)\n}\n\
             interface Default {\nstatic func default() -> Self\n}\n\
             func main() {}",
            &[
                (StdItem::PartialEq, "PartialEq"),
                (StdItem::Hashable, "Hashable"),
                (StdItem::Default, "Default"),
            ],
            |bodies, gcx| {
                let span = bodies[0].locals[bodies[0].return_local].span;
                for item in [StdItem::PartialEq, StdItem::Hashable, StdItem::Default] {
                    let id = declaration(gcx, item, span).expect("synthetic tuple declaration");
                    let definition = gcx
                        .store
                        .synthetic_definitions
                        .borrow()
                        .get(&id)
                        .unwrap()
                        .clone();
                    let wire = crate::metadata::wire::synthetic_definition_to_wire(gcx.symbols(), id, &definition);
                    let bytes = bincode::serialize(&wire).unwrap();
                    let restored = bincode::deserialize(&bytes).unwrap();
                    let files = rustc_hash::FxHashMap::default();
                    let (restored_id, decoded) = crate::metadata::wire::synthetic_definition_from_wire(
                        gcx,
                        &restored,
                        crate::metadata::wire::FileRemap { old_to_new: &files },
                    );
                    assert_eq!(restored_id, id);
                    assert_eq!(decoded.kind, SyntheticDefinitionKind::TupleConformance(item));
                    assert!(validate_declaration(gcx, &decoded).is_ok());
                }
            },
        );
    }
}
