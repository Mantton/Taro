use crate::{
    compile::context::GlobalContext,
    error::CompileResult,
    hir::DefinitionID,
    mir::{
        BasicBlockData, BasicBlockId, Body, CallUnwindAction, Constant, ConstantKind, LocalDecl,
        LocalId, LocalKind, MirPackage, Operand, Place, Terminator, TerminatorKind,
        builder::MirBuilder,
        optimize::{
            self,
            async_transform::{AsyncRuntimeFn, find_or_register_async_runtime_function},
        },
        pretty::PrettyPrintMir,
    },
    sema::{
        models::{GenericArguments, LabeledFunctionSignature, Ty},
        tycheck::utils::generics::GenericsBuilder,
    },
    thir,
};
use rustc_hash::FxHashMap;

pub fn build_package<'ctx>(
    package: thir::ThirPackage<'ctx>,
    gcx: GlobalContext<'ctx>,
) -> CompileResult<&'ctx MirPackage<'ctx>> {
    let async_entry = package.entry.and_then(|entry| {
        package.functions.get(&entry).and_then(|func| {
            func.is_async
                .then_some((entry, gcx.function_body_output(entry)))
        })
    });

    // Phase 1: Build MIR for all functions and run local passes
    // Local passes (prune, simplify, validate) don't need other function bodies
    let mut bodies: FxHashMap<DefinitionID, Body<'ctx>> = FxHashMap::default();

    for (id, func) in package.functions {
        if func.body.is_none() {
            continue;
        }
        let mut body = MirBuilder::build_function(gcx, &func);

        // Run local passes (prune, simplify, validate)
        optimize::run_local_passes(gcx, &mut body)?;

        bodies.insert(id, body);
    }

    // Async lowering needs source-form escape summaries, but it must itself
    // finish package-wide before canonical MIR is published. Otherwise an
    // earlier caller could see a source-form async body while a later caller
    // sees the constructor that codegen actually consumes.
    let source_functions = bodies
        .iter()
        .map(|(&id, body)| {
            let body = gcx.store.arenas.mir_bodies.alloc(body.clone());
            (id, &*body)
        })
        .collect();
    optimize::escape::compute_escape_summaries(gcx, &source_functions);

    let mut pending: Vec<_> = bodies.into_iter().collect();
    pending.sort_by_key(|(id, _)| *id);
    let mut canonical_bodies = FxHashMap::default();
    let mut cursor = 0usize;
    while cursor < pending.len() {
        let (id, mut body) = pending[cursor].clone();
        cursor += 1;
        optimize::lower_async_for_canonical_mir(gcx, &mut body)?;
        canonical_bodies.insert(id, body);

        let mut queued: Vec<_> = gcx.take_queued_mir_bodies().into_iter().collect();
        queued.sort_by_key(|(queued_id, _)| *queued_id);
        for (queued_id, mut queued_body) in queued {
            optimize::run_local_passes(gcx, &mut queued_body)?;
            pending.push((queued_id, queued_body));
        }
    }

    // Publish canonical inline MIR before any interprocedural pass runs. Final
    // MIR is stored separately below; this keeps source and metadata builds on
    // exactly the same inlining representation.
    let mut functions: FxHashMap<DefinitionID, &'ctx Body<'ctx>> = FxHashMap::default();
    for (id, body) in canonical_bodies {
        let alloc = gcx.store.arenas.mir_bodies.alloc(body);
        functions.insert(id, alloc);
    }

    let mut pkg = MirPackage::default();
    pkg.functions = functions;
    pkg.entry = package.entry;
    let pkg = gcx.store.alloc_mir_package(pkg);
    gcx.store
        .inline_mir_packages
        .borrow_mut()
        .insert(gcx.package_index(), pkg);

    // Recompute summaries from the same canonical constructor/poll/drop forms
    // consumed by every global interprocedural pass.
    optimize::escape::compute_escape_summaries(gcx, &pkg.functions);

    // Phase 2: Run global passes (inlining, lowering, escape analysis, safepoints)
    // These passes need access to other function bodies
    let mut final_functions: FxHashMap<DefinitionID, &'ctx Body<'ctx>> = FxHashMap::default();
    let pending: Vec<(DefinitionID, Body<'ctx>)> = pkg
        .functions
        .iter()
        .map(|(&def_id, body)| (def_id, (**body).clone()))
        .collect();
    let mut cursor = 0usize;

    while cursor < pending.len() {
        let (def_id, mut body) = pending[cursor].clone();
        cursor += 1;

        optimize::run_global_passes(gcx, &mut body)?;

        let alloc = gcx.store.arenas.mir_bodies.alloc(body);
        final_functions.insert(def_id, alloc);

        debug_assert!(
            gcx.take_queued_mir_bodies().is_empty(),
            "async MIR was synthesized after canonical publication"
        );
    }

    let final_entry = if let Some((entry_id, entry_output)) = async_entry {
        let mut wrapper = build_async_entry_wrapper(gcx, entry_id, entry_output)?;
        optimize::run_local_passes(gcx, &mut wrapper)?;
        let wrapper_id = wrapper.owner;
        let canonical = gcx.store.arenas.mir_bodies.alloc(wrapper.clone());
        publish_inline_body(gcx, wrapper_id, canonical, Some(wrapper_id));
        optimize::run_global_passes(gcx, &mut wrapper)?;
        let alloc = gcx.store.arenas.mir_bodies.alloc(wrapper);
        final_functions.insert(wrapper_id, alloc);
        Some(wrapper_id)
    } else {
        package.entry
    };

    let mut final_pkg = MirPackage::default();
    final_pkg.functions = final_functions;
    final_pkg.entry = final_entry;
    let final_pkg = gcx.store.alloc_mir_package(final_pkg);

    // Update the stored package with the fully optimized version
    gcx.store
        .mir_packages
        .borrow_mut()
        .insert(gcx.package_index(), final_pkg);

    if gcx.config.debug.dump_mir {
        eprintln!("\n=== MIR Dump for {} ===", gcx.config.name);
        for (def_id, body) in final_pkg.functions.iter() {
            let symbol = gcx.definition_symbol_or_fallback(*def_id);
            eprintln!("\nfn {}() {{", symbol);
            let pretty = PrettyPrintMir { body, gcx };
            eprintln!("{}", pretty);
            eprintln!("}}");
        }
        eprintln!("=== End MIR Dump ===\n");
    }

    Ok(final_pkg)
}

fn publish_inline_body<'ctx>(
    gcx: GlobalContext<'ctx>,
    def_id: DefinitionID,
    body: &'ctx Body<'ctx>,
    entry: Option<DefinitionID>,
) {
    let current = gcx
        .store
        .inline_mir_packages
        .borrow()
        .get(&gcx.package_index())
        .copied();
    let mut functions = current
        .map(|package| package.functions.clone())
        .unwrap_or_default();
    functions.insert(def_id, body);
    let package = gcx.store.alloc_mir_package(MirPackage { functions, entry });
    gcx.store
        .inline_mir_packages
        .borrow_mut()
        .insert(gcx.package_index(), package);
}

fn build_async_entry_wrapper<'ctx>(
    gcx: GlobalContext<'ctx>,
    entry_id: DefinitionID,
    output_ty: Ty<'ctx>,
) -> CompileResult<Body<'ctx>> {
    let span = gcx.definition_ident(entry_id).span;
    let wrapper_id = register_async_entry_definition(gcx, entry_id, output_ty, span);
    let handle_ty = gcx.async_handle_ty();
    let output_storage_ty = if output_ty == gcx.types.void {
        gcx.types.uint8
    } else {
        output_ty
    };
    let output_ref_ty = gcx
        .store
        .interners
        .intern_ty(crate::sema::models::TyKind::Reference(
            output_storage_ty,
            crate::hir::Mutability::Mutable,
        ));
    let output_ptr_ty = gcx
        .store
        .interners
        .intern_ty(crate::sema::models::TyKind::Pointer(
            output_storage_ty,
            crate::hir::Mutability::Mutable,
        ));
    let output_raw_ty = gcx
        .store
        .interners
        .intern_ty(crate::sema::models::TyKind::Pointer(
            gcx.types.uint8,
            crate::hir::Mutability::Mutable,
        ));

    let mut body = Body {
        owner: wrapper_id,
        source_scopes: Body::initial_source_scopes(wrapper_id),
        locals: Default::default(),
        basic_blocks: Default::default(),
        start_block: BasicBlockId::from_raw(0),
        return_local: LocalId::from_raw(0),
        escape_locals: vec![],
        phase: crate::mir::MirPhase::Built,
        is_async: false,
    };

    let return_local = push_local(
        &mut body,
        output_ty,
        LocalKind::Return,
        true,
        Some(gcx.intern_symbol("$ret")),
        span,
    );
    body.return_local = return_local;
    let output_storage_local = if output_ty == gcx.types.void {
        Some(push_local(
            &mut body,
            gcx.types.uint8,
            LocalKind::Temp,
            true,
            Some(gcx.intern_symbol("$main_out_dummy")),
            span,
        ))
    } else {
        None
    };
    let handle_local = push_local(
        &mut body,
        handle_ty,
        LocalKind::Temp,
        true,
        Some(gcx.intern_symbol("$main_handle")),
        span,
    );
    let output_ref_local = push_local(
        &mut body,
        output_ref_ty,
        LocalKind::Temp,
        true,
        Some(gcx.intern_symbol("$main_out_ref")),
        span,
    );
    let output_ptr_local = push_local(
        &mut body,
        output_ptr_ty,
        LocalKind::Temp,
        true,
        Some(gcx.intern_symbol("$main_out_ptr")),
        span,
    );
    let output_raw_local = push_local(
        &mut body,
        output_raw_ty,
        LocalKind::Temp,
        true,
        Some(gcx.intern_symbol("$main_out_raw")),
        span,
    );
    let run_root_void_local = push_local(
        &mut body,
        gcx.types.void,
        LocalKind::Temp,
        true,
        Some(gcx.intern_symbol("$main_run_void")),
        span,
    );

    let entry_block = body.basic_blocks.push(BasicBlockData {
        note: Some("async-entry-call".into()),
        statements: vec![],
        terminator: None,
    });
    let prepare_block = body.basic_blocks.push(BasicBlockData {
        note: Some("async-entry-prepare".into()),
        statements: vec![
            crate::mir::Statement {
                kind: crate::mir::StatementKind::Assign(
                    Place::from_local(output_ref_local),
                    crate::mir::Rvalue::Ref {
                        mutable: true,
                        place: Place::from_local(output_storage_local.unwrap_or(return_local)),
                    },
                ),
                span,
            },
            crate::mir::Statement {
                kind: crate::mir::StatementKind::Assign(
                    Place::from_local(output_ptr_local),
                    crate::mir::Rvalue::Cast {
                        operand: Operand::Copy(Place::from_local(output_ref_local)),
                        ty: output_ptr_ty,
                        kind: crate::mir::CastKind::Pointer,
                    },
                ),
                span,
            },
            crate::mir::Statement {
                kind: crate::mir::StatementKind::Assign(
                    Place::from_local(output_raw_local),
                    crate::mir::Rvalue::Cast {
                        operand: Operand::Copy(Place::from_local(output_ptr_local)),
                        ty: output_raw_ty,
                        kind: crate::mir::CastKind::Pointer,
                    },
                ),
                span,
            },
        ],
        terminator: None,
    });
    let ret_block = body.basic_blocks.push(BasicBlockData {
        note: Some("async-entry-ret".into()),
        statements: vec![],
        terminator: Some(Terminator {
            kind: TerminatorKind::Return,
            span,
        }),
    });
    body.start_block = entry_block;

    let entry_ty = gcx.get_type(entry_id);
    body.basic_blocks[entry_block].terminator = Some(Terminator {
        kind: TerminatorKind::Call {
            func: fn_operand(
                entry_id,
                GenericsBuilder::identity_for_item(gcx, entry_id),
                entry_ty,
            ),
            args: vec![],
            devirt_hint: None,
            destination: Place::from_local(handle_local),
            target: prepare_block,
            unwind: CallUnwindAction::Terminate,
        },
        span,
    });

    let run_root_id = find_or_register_async_runtime_function(gcx, AsyncRuntimeFn::RunRoot, span);
    let run_root_ty = gcx.get_type(run_root_id);
    body.basic_blocks[prepare_block].terminator = Some(Terminator {
        kind: TerminatorKind::Call {
            func: fn_operand(run_root_id, GenericArguments::empty(), run_root_ty),
            args: vec![
                Operand::Copy(Place::from_local(handle_local)),
                Operand::Copy(Place::from_local(output_raw_local)),
            ],
            devirt_hint: None,
            destination: Place::from_local(run_root_void_local),
            target: ret_block,
            unwind: CallUnwindAction::Terminate,
        },
        span,
    });

    Ok(body)
}

fn register_async_entry_definition<'ctx>(
    gcx: GlobalContext<'ctx>,
    entry_id: DefinitionID,
    output_ty: Ty<'ctx>,
    span: crate::span::Span,
) -> DefinitionID {
    let wrapper_id = gcx.allocate_synthetic_id(entry_id.package());
    let signature = LabeledFunctionSignature {
        inputs: vec![],
        output: output_ty,
        is_variadic: false,
        abi: None,
    };
    let signature_ref = gcx
        .store
        .arenas
        .function_signatures
        .alloc(signature.clone());
    let entry_name = gcx.definition_symbol_or_fallback(entry_id);
    let def = crate::sema::models::SyntheticDefinition {
        name: gcx.intern_symbol(&format!("{}$async_entry", gcx.symbol_text(entry_name))),
        generics: gcx
            .store
            .arenas
            .generics
            .alloc(crate::sema::models::Generics {
                parameters: vec![],
                has_self: false,
                parent: None,
                parent_count: 0,
            }),
        signature: signature_ref,
        span,
    };
    gcx.register_synthetic_definition(wrapper_id, def);
    gcx.cache_type(wrapper_id, Ty::from_labeled_signature(gcx, &signature));
    wrapper_id
}

fn push_local<'ctx>(
    body: &mut Body<'ctx>,
    ty: Ty<'ctx>,
    kind: LocalKind,
    mutable: bool,
    name: Option<crate::span::Symbol>,
    span: crate::span::Span,
) -> LocalId {
    let local = body.locals.push(LocalDecl {
        ty,
        kind,
        mutable,
        name,
        span,
    });
    body.escape_locals.push(false);
    local
}

fn fn_operand<'ctx>(
    def_id: DefinitionID,
    generic_args: crate::sema::models::GenericArguments<'ctx>,
    ty: Ty<'ctx>,
) -> Operand<'ctx> {
    Operand::Constant(Constant {
        ty,
        value: ConstantKind::Function(def_id, generic_args, ty),
    })
}
