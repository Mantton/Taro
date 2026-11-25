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
use std::collections::VecDeque;

pub fn build_package<'ctx>(
    package: thir::ThirPackage<'ctx>,
    gcx: GlobalContext<'ctx>,
) -> CompileResult<&'ctx MirPackage<'ctx>> {
    build_package_with_vet(package, gcx, false)
}

pub(crate) fn build_package_with_vet<'ctx>(
    package: thir::ThirPackage<'ctx>,
    gcx: GlobalContext<'ctx>,
    vet: bool,
) -> CompileResult<&'ctx MirPackage<'ctx>> {
    let mut findings = Vec::new();
    let async_entry = package.entry.and_then(|entry| {
        package.functions.get(&entry).and_then(|func| {
            func.is_async
                .then_some((entry, gcx.function_body_output(entry)))
        })
    });

    // Phase 1: Build MIR for all functions and run local passes
    // Local passes (prune, simplify, validate) don't need other function bodies
    let mut pending = Vec::new();

    for (id, func) in package.functions {
        if func.body.is_none() {
            continue;
        }
        // Some compiler-generated bodies obtain signatures from the synthetic
        // registry. Persist those too: imported ownership certificates are
        // validated before that registry is installed during hydration.
        let missing_signature =
            gcx.with_session_type_database(|db| !db.def_to_fn_sig.contains_key(&id));
        if missing_signature {
            gcx.cache_signature(id, gcx.get_signature(id).clone());
        }
        let mut body = MirBuilder::build_function(gcx, &func);
        if vet {
            findings.extend(crate::mir::vet::check_body(gcx, &body));
        }

        // Run local passes (prune, simplify, validate)
        let adapter = gcx.store.synthetic_definitions.borrow().get(&id).is_some_and(|definition|
            matches!(definition.kind, crate::sema::models::SyntheticDefinitionKind::AdoptedClassDefault { .. }
                | crate::sema::models::SyntheticDefinitionKind::AdoptedClassDefaultArgument { .. }));
        if !adapter {
            optimize::run_local_passes(gcx, &mut body)?;
        }

        pending.push((id, body));
    }

    pending.sort_by_key(|(id, _)| *id);
    crate::mir::class_defaults::collect(gcx, pending.iter().map(|(_, body)| body))?;

    // Exact default calls need the original generic body's conditional proofs.
    // Check forwarding bodies only after those facts have been published.
    for (id, body) in &mut pending {
        let adapter = gcx.store.synthetic_definitions.borrow().get(id).is_some_and(|definition|
            matches!(definition.kind, crate::sema::models::SyntheticDefinitionKind::AdoptedClassDefault { .. }
                | crate::sema::models::SyntheticDefinitionKind::AdoptedClassDefaultArgument { .. }));
        if adapter {
            optimize::run_local_passes(gcx, body)?;
        }
    }

    // The entry wrapper participates in the same canonical/global pipeline as
    // every other function, including the poll/drop bodies queued below.
    let entry = if let Some((entry_id, output_ty)) = async_entry {
        let mut wrapper = build_async_entry_wrapper(gcx, entry_id, output_ty)?;
        optimize::run_local_passes(gcx, &mut wrapper)?;
        let wrapper_id = wrapper.owner;
        pending.push((wrapper_id, wrapper));
        Some(wrapper_id)
    } else {
        package.entry
    };

    // Async lowering applies a conservative source-form bridge before frame
    // construction. Concrete constructor/poll/drop summaries are computed
    // later from shared MIR when their instances are requested by codegen.
    pending.sort_by_key(|(id, _)| *id);
    let mut pending = VecDeque::from(pending);
    let mut functions: FxHashMap<DefinitionID, &'ctx Body<'ctx>> = FxHashMap::default();
    while let Some((id, mut body)) = pending.pop_front() {
        optimize::lower_async_for_canonical_mir(gcx, &mut body)?;
        functions.insert(id, gcx.store.arenas.mir_bodies.alloc(body));

        let mut queued: Vec<_> = gcx.take_queued_mir_bodies().into_iter().collect();
        queued.sort_by_key(|(queued_id, _)| *queued_id);
        for (queued_id, mut queued_body) in queued {
            optimize::run_local_passes(gcx, &mut queued_body)?;
            pending.push_back((queued_id, queued_body));
        }
    }

    // Publish canonical inline MIR before any interprocedural pass runs. Final
    // MIR is stored separately below; this keeps source and metadata builds on
    // exactly the same inlining representation.
    let pkg = gcx.store.alloc_mir_package(MirPackage { functions, entry });
    gcx.store
        .inline_mir_packages
        .borrow_mut()
        .insert(gcx.package_index(), pkg);

    // Phase 2: Run shared global passes before instance placement/safepoints.
    // These passes need access to other function bodies
    let mut final_functions: FxHashMap<DefinitionID, &'ctx Body<'ctx>> = FxHashMap::default();
    for (&def_id, canonical) in &pkg.functions {
        let mut body = (**canonical).clone();
        optimize::run_global_passes(gcx, &mut body)?;

        let alloc = gcx.store.arenas.mir_bodies.alloc(body);
        final_functions.insert(def_id, alloc);

        debug_assert!(
            gcx.take_queued_mir_bodies().is_empty(),
            "async MIR was synthesized after canonical publication"
        );
    }

    let final_pkg = gcx.store.alloc_mir_package(MirPackage {
        functions: final_functions,
        entry,
    });

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

    if vet {
        // Shadowing is decided during name resolution.
        if let Some(facts) = gcx.store.lint_facts.borrow().get(&gcx.package_index()) {
            findings.extend(facts.shadowed.iter().map(|(span, message)| {
                crate::mir::vet::Finding {
                    span: *span,
                    message: message.clone(),
                }
            }));
        }
    }
    if !findings.is_empty() {
        findings.sort_by_key(|finding| {
            (
                finding.span.file,
                finding.span.start.line,
                finding.span.start.offset,
                finding.message.clone(),
            )
        });
        findings.dedup();
        for finding in findings {
            gcx.dcx().emit_warning(finding.message, Some(finding.span));
        }
        return Err(crate::error::ReportedError);
    }
    Ok(final_pkg)
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
        // Fresh compiler bootstrap: all storage is primitive/raw, and run_main
        // synchronously consumes the fresh native entry frame. No source
        // reference is formed, erased, retained or leaked at this boundary.
        escape_locals: Vec::new(),

        owner: wrapper_id,
        source_scopes: Body::initial_source_scopes(wrapper_id),
        locals: Default::default(),
        basic_blocks: Default::default(),
        start_block: BasicBlockId::from_raw(0),
        return_local: LocalId::from_raw(0),
        phase: crate::mir::MirPhase::Built,
        is_async: false,
        generator_element_ty: None,
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
            // Entry results are primitive status/unit storage. Initialize the
            // storage before forming a valid mutable reference for the ABI.
            crate::mir::Statement {
                kind: crate::mir::StatementKind::Assign(
                    Place::from_local(output_storage_local.unwrap_or(return_local)),
                    crate::mir::Rvalue::Zeroed {
                        ty: output_storage_ty,
                    },
                ),
                span,
            },
            crate::mir::Statement {
                kind: crate::mir::StatementKind::Assign(
                    Place::from_local(output_ptr_local),
                    crate::mir::Rvalue::CleanupAddress {
                        place: Place::from_local(output_storage_local.unwrap_or(return_local)),
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
            destination: Place::from_local(handle_local),
            target: prepare_block,
            unwind: CallUnwindAction::Terminate,
        },
        span,
    });

    let run_root_id = find_or_register_async_runtime_function(gcx, AsyncRuntimeFn::RunMain, span);
    let run_root_ty = gcx.get_type(run_root_id);
    body.basic_blocks[prepare_block].terminator = Some(Terminator {
        kind: TerminatorKind::Call {
            func: fn_operand(run_root_id, GenericArguments::empty(), run_root_ty),
            args: vec![
                Operand::Copy(Place::from_local(handle_local)),
                Operand::Copy(Place::from_local(output_raw_local)),
            ],
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
        kind: crate::sema::models::SyntheticDefinitionKind::Ordinary,
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
