//! Callable witnesses for safe Taro function pointers. One declaration per
//! callable kind is instantiated for the complete signature, so tuple arities
//! and layouts never share a concrete implementation by accident.
use crate::{
    compile::context::Gcx,
    error::{CompileResult, ReportedError},
    hir::DefinitionID,
    mir::{
        BasicBlockData, Body, CallUnwindAction, LocalDecl, LocalKind, MirPhase, Operand, Place,
        PlaceElem, Terminator, TerminatorKind,
    },
    sema::{
        models::{
            ClosureKind, GenericArgument, GenericParameter, GenericParameterDefinition,
            GenericParameterDefinitionKind, Generics, LabeledFunctionParameter,
            LabeledFunctionSignature, SyntheticDefinition, SyntheticDefinitionKind, Ty, TyKind,
        },
        tycheck::utils::normalize_post_monomorphization,
    },
    span::Span,
    specialize::Instance,
};
use index_vec::IndexVec;

pub(crate) fn declaration(gcx: Gcx<'_>, kind: ClosureKind, span: Span) -> DefinitionID {
    let kind = SyntheticDefinitionKind::FunctionPointerCall {
        is_async: kind == ClosureKind::AsyncFn,
    };
    if let Some(id) = gcx
        .store
        .synthetic_definitions
        .borrow()
        .iter()
        .find_map(|(id, def)| {
            (id.package() == gcx.package_index() && def.kind == kind).then_some(*id)
        })
    {
        return id;
    }
    let id = gcx.allocate_synthetic_id(gcx.package_index());
    let mut parameters = Vec::new();
    let mut types = Vec::new();
    for (index, name) in ["F", "Args", "Output"].into_iter().enumerate() {
        let name = gcx.intern_symbol(name);
        parameters.push(GenericParameterDefinition {
            name,
            id: gcx.allocate_synthetic_id(gcx.package_index()),
            index,
            kind: GenericParameterDefinitionKind::Type { default: None },
        });
        types.push(Ty::new(
            TyKind::Parameter(GenericParameter { index, name }),
            gcx,
        ));
    }
    let generics = gcx.store.arenas.generics.alloc(Generics {
        parameters,
        has_self: false,
        parent: None,
        parent_count: 0,
    });
    let parameter = |name: &str, ty| LabeledFunctionParameter {
        name: gcx.intern_symbol(name),
        label: None,
        default_provider: None,
        ty,
    };
    let signature = gcx
        .store
        .arenas
        .function_signatures
        .alloc(LabeledFunctionSignature {
            inputs: vec![parameter("self", types[0]), parameter("args", types[1])],
            output: types[2],
            is_variadic: false,
            abi: None,
        });
    gcx.register_synthetic_definition(
        id,
        SyntheticDefinition {
            kind,
            name: gcx.intern_symbol(
                if matches!(
                    kind,
                    SyntheticDefinitionKind::FunctionPointerCall { is_async: true }
                ) {
                    "$asyncFunctionPointerCall"
                } else {
                    "$functionPointerCall"
                },
            ),
            generics,
            signature,
            span,
        },
    );
    gcx.cache_type(id, Ty::from_labeled_signature(gcx, signature));
    id
}

pub(crate) fn validate_declaration(def: &SyntheticDefinition<'_>) -> Result<(), &'static str> {
    if !matches!(
        def.kind,
        SyntheticDefinitionKind::FunctionPointerCall { .. }
    ) {
        return Ok(());
    }
    let sig = def.signature;
    if def.generics.parameters.len() != 3
        || def.generics.has_self
        || def.generics.parent.is_some()
        || def.generics.parent_count != 0
        || sig.abi.is_some()
        || sig.is_variadic
        || sig.inputs.len() != 2
    {
        return Err("function-pointer callable metadata has invalid declaration");
    }
    for (index, parameter) in def.generics.parameters.iter().enumerate() {
        if parameter.index != index
            || !matches!(
                parameter.kind,
                GenericParameterDefinitionKind::Type { default: None }
            )
        {
            return Err("function-pointer callable metadata has invalid generics");
        }
    }
    for (index, ty) in [sig.inputs[0].ty, sig.inputs[1].ty, sig.output]
        .into_iter()
        .enumerate()
    {
        if !matches!(ty.kind(), TyKind::Parameter(p) if p.index == index && p.name == def.generics.parameters[index].name)
        {
            return Err("function-pointer callable metadata has invalid signature");
        }
    }
    if sig
        .inputs
        .iter()
        .any(|p| p.label.is_some() || p.default_provider.is_some())
    {
        return Err("function-pointer callable metadata has invalid parameters");
    }
    Ok(())
}

pub(crate) fn build_body<'ctx>(
    gcx: Gcx<'ctx>,
    instance: Instance<'ctx>,
) -> CompileResult<Body<'ctx>> {
    let owner = instance.def_id();
    let def = gcx
        .store
        .synthetic_definitions
        .borrow()
        .get(&owner)
        .cloned()
        .ok_or(ReportedError)?;
    let span = def.span;
    let error = |message: &str| {
        gcx.dcx().emit_error(message.into(), Some(span));
        ReportedError
    };
    validate_declaration(&def).map_err(error)?;
    let SyntheticDefinitionKind::FunctionPointerCall { is_async } = def.kind else {
        return Err(error("incorrect function-pointer helper kind"));
    };
    let [
        GenericArgument::Type(function),
        GenericArgument::Type(args),
        GenericArgument::Type(output),
    ] = &instance.args()[..]
    else {
        return Err(error("function-pointer call requires three concrete types"));
    };
    let function = normalize_post_monomorphization(gcx, *function);
    let args = normalize_post_monomorphization(gcx, *args);
    let output = normalize_post_monomorphization(gcx, *output);
    let Some((kind, inputs, actual_output)) = crate::sema::models::callable_signature(function)
    else {
        return Err(error(
            "safe Taro function pointer required for callable witness",
        ));
    };
    if !matches!(function.kind(), TyKind::FnPointer { .. })
        || (kind == ClosureKind::AsyncFn) != is_async
        || actual_output != output
        || args != crate::sema::models::callable_args_ty(gcx, inputs)
    {
        return Err(error(
            "function-pointer callable signature does not match its witness",
        ));
    }
    let machine_output = if is_async {
        gcx.async_handle_ty()
    } else {
        output
    };
    let mut locals = IndexVec::new();
    let local = |ty, kind| LocalDecl {
        ty,
        kind,
        mutable: true,
        name: None,
        span,
    };
    let return_local = locals.push(local(machine_output, LocalKind::Return));
    let callee = locals.push(local(function, LocalKind::Param));
    let packed = locals.push(local(args, LocalKind::Param));
    let mut blocks: IndexVec<crate::mir::BasicBlockId, BasicBlockData<'ctx>> = IndexVec::new();
    let start_block = blocks.push(BasicBlockData {
        note: Some("function-pointer callable adapter".into()),
        statements: vec![],
        terminator: None,
    });
    let end = blocks.push(BasicBlockData {
        note: None,
        statements: vec![],
        terminator: Some(Terminator {
            span,
            kind: TerminatorKind::Return,
        }),
    });
    let unwind = blocks.push(BasicBlockData {
        note: None,
        statements: vec![],
        terminator: Some(Terminator {
            span,
            kind: TerminatorKind::ResumeUnwind,
        }),
    });
    let arguments = inputs
        .iter()
        .enumerate()
        .map(|(index, &ty)| {
            Operand::Copy(Place {
                local: packed,
                projection: vec![PlaceElem::Field(
                    crate::thir::FieldIndex::from_raw(index as u32),
                    ty,
                )],
            })
        })
        .collect();
    blocks[start_block].terminator = Some(Terminator {
        span,
        kind: TerminatorKind::Call {
            func: Operand::Copy(Place::from_local(callee)),
            args: arguments,
            destination: Place::from_local(return_local),
            target: end,
            unwind: CallUnwindAction::Cleanup(unwind),
        },
    });
    Ok(Body {
        owner,
        source_scopes: Body::initial_source_scopes(owner),
        locals,
        basic_blocks: blocks,
        start_block,
        return_local,
        phase: MirPhase::CfgClean,
        is_async: false,
        escape_locals: vec![],
    })
}
