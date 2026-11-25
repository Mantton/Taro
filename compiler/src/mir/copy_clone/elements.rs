//! Tuple/array/closure Clone stages completed elements in rooted locals.
//! Nontrivial fixed arrays initially generate O(length) MIR; intrinsic-copy
//! arrays retain their bulk-copy path. S44 may replace staging with a loop only
//! when partial initialization stays rooted across later calls.
//! Only the final safepoint-free block moves them into the whole return value.
use super::*;
use crate::{
    hir::StdItem,
    mir::{BasicBlockId, CallUnwindAction, Constant, ConstantKind, LocalId},
    sema::models::{
        ConstKind, ConstValue, GenericArguments, GoalResult, InterfaceGoal, SelectionMode,
    },
    sema::tycheck::utils::instantiate::instantiate_ty_with_args,
    thir::FieldIndex,
};

pub(super) fn build_body<'ctx>(
    gcx: Gcx<'ctx>,
    owner: DefinitionID,
    ty: Ty<'ctx>,
    span: Span,
) -> CompileResult<Body<'ctx>> {
    let error = |message: &str| {
        gcx.dcx().emit_error(message.into(), Some(span));
        ReportedError
    };
    let (fields, required_components) = match ty.kind() {
        TyKind::Tuple(fields) => (fields.to_vec(), fields.to_vec()),
        TyKind::Closure { .. } => {
            let fields = crate::sema::impl_engine::closure_clone_fields(gcx, ty)
                .ok_or_else(|| error("closure Clone requires capture metadata"))?;
            (fields.clone(), fields)
        }
        TyKind::Array { element, len } => {
            let ConstKind::Value(ConstValue::Integer(count)) = len.kind else {
                return Err(error("array Clone requires a concrete length"));
            };
            let count = u32::try_from(count)
                .map_err(|_| error("array Clone length exceeds the static projection limit"))?
                as usize;
            (vec![element; count], vec![element])
        }
        _ => {
            return Err(error(
                "element-wise Clone requires a tuple, fixed array or closure",
            ));
        }
    };
    let clone_id = gcx
        .std_item_def(StdItem::Clone)
        .ok_or_else(|| error("tuple Clone requires Clone"))?;
    let requirements = gcx
        .get_interface_requirements(clone_id)
        .ok_or_else(|| error("missing Clone requirements"))?;
    let method = requirements
        .methods
        .iter()
        .find(|method| gcx.symbol_eq(method.name, "clone"))
        .ok_or_else(|| error("missing Clone method"))?
        .id;
    for field in &required_components {
        let goal = InterfaceGoal {
            interface_id: clone_id,
            self_ty: *field,
            interface_args: GenericArguments::empty(),
            bindings: &[],
            param_env: &[],
        };
        if gcx.prove_interface_goal(goal, SelectionMode::Codegen) != GoalResult::Proven {
            return Err(error(
                "element-wise Clone requires every component to implement Clone",
            ));
        }
    }
    let mut locals = IndexVec::new();
    let return_local = locals.push(LocalDecl {
        ty,
        kind: LocalKind::Return,
        mutable: true,
        name: None,
        span,
    });
    let parameter = locals.push(LocalDecl {
        ty,
        kind: LocalKind::Param,
        mutable: false,
        name: None,
        span,
    });
    let mut blocks = IndexVec::new();
    let start_block = blocks.push(BasicBlockData {
        note: Some("begin element-wise Clone".into()),
        statements: vec![],
        terminator: None,
    });
    let resume = blocks.push(BasicBlockData {
        note: None,
        statements: vec![],
        terminator: Some(Terminator {
            kind: TerminatorKind::ResumeUnwind,
            span,
        }),
    });
    let mut body = Body {
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
    let mut current = start_block;
    let unwind = resume;
    let mut completed = Vec::new();
    for (index, field_ty) in fields.iter().copied().enumerate() {
        let result = temp(&mut body, field_ty, span);
        let after = block(&mut body, "next cloned element");
        let component = Place {
            local: parameter,
            projection: vec![PlaceElem::Field(FieldIndex::from_usize(index), field_ty)],
        };
        let args = gcx
            .store
            .interners
            .intern_generic_args(vec![GenericArgument::Type(field_ty)]);
        let signature = instantiate_ty_with_args(
            gcx,
            Ty::from_labeled_signature(gcx, gcx.get_signature(method)),
            args,
        );
        body.basic_blocks[current].terminator = Some(Terminator {
            span,
            kind: TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: signature,
                    value: ConstantKind::Function(method, args, signature),
                }),
                args: vec![Operand::Copy(component)],
                destination: Place::from_local(result),
                target: after,
                unwind: CallUnwindAction::Cleanup(unwind),
            },
        });
        completed.push((result, field_ty));
        current = after;
    }
    for (index, (local, field_ty)) in completed.into_iter().enumerate() {
        let mut destination = Place::from_local(return_local);
        destination
            .projection
            .push(PlaceElem::Field(FieldIndex::from_usize(index), field_ty));
        body.basic_blocks[current].statements.push(Statement {
            span,
            kind: StatementKind::Assign(
                destination,
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
    // The generic declaration is validated against this concrete body by the
    // instance pipeline. Here only prune unused cleanup suffixes/CFG debris.
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sema::models::SyntheticDefinitionKind;

    #[test]
    fn element_clones_run_in_order_and_unwind_without_source_destructors() {
        crate::test_support::analyze_script_built_mir_with_items(
            "interface Clone {\nfunc clone() -> Self\n}\nstruct Token { value: int32 }\nconform Token to Clone {\nfunc clone() -> Token { Token { value: self.value } }\n}\nfunc read(_ token: &Token) -> int32 { token.value }\nfunc main() { a := Token { value: 1 }; b := Token { value: 2 }; c := Token { value: 3 }; f := () => read(&a) + read(&b) + read(&c) }",
            &[(StdItem::Clone, "Clone")],
            |bodies, gcx| {
                let closure = bodies
                    .iter()
                    .flat_map(|body| body.locals.iter())
                    .map(|local| local.ty)
                    .find(|ty| matches!(ty.kind(), TyKind::Closure { .. }))
                    .expect("closure environment");
                let TyKind::Closure { .. } = closure.kind() else {
                    unreachable!()
                };
                let token = bodies
                    .iter()
                    .find(|body| gcx.symbol_text(gcx.definition_symbol_or_fallback(body.owner)).as_str() == "read")
                    .map(|body| {
                        body.locals
                            .iter()
                            .find(|local| local.kind == LocalKind::Param)
                            .unwrap()
                            .ty
                            .dereference()
                            .unwrap()
                    })
                    .unwrap();
                let tuple = Ty::new(
                    TyKind::Tuple(gcx.store.interners.intern_ty_list(vec![token; 3])),
                    gcx,
                );
                let array = Ty::new(
                    TyKind::Array {
                        element: token,
                        len: crate::sema::models::Const {
                            ty: gcx.types.uint,
                            kind: ConstKind::Value(ConstValue::Integer(3)),
                        },
                    },
                    gcx,
                );
                let span = bodies[0].locals[bodies[0].return_local].span;
                for (ty, kind) in [
                    (tuple, SyntheticDefinitionKind::TupleClone),
                    (array, SyntheticDefinitionKind::ArrayClone),
                    (closure, SyntheticDefinitionKind::ClosureClone),
                ] {
                    let owner = crate::mir::copy_clone::declaration_with_kind(gcx, span, kind);
                    let args = gcx
                        .store
                        .interners
                        .intern_generic_args(vec![GenericArgument::Type(ty)]);
                    let body = crate::mir::copy_clone::build_body(gcx, Instance::item(owner, args))
                        .unwrap_or_else(|_| panic!("element Clone body"));
                    let mut cursor = body.start_block;
                    let mut indices = vec![];
                    loop {
                        let data = &body.basic_blocks[cursor];
                        match &data.terminator.as_ref().unwrap().kind {
                            TerminatorKind::Goto { target } => cursor = *target,
                            TerminatorKind::Call {
                                target,
                                unwind: CallUnwindAction::Cleanup(failure),
                                ..
                            } => {
                                let TerminatorKind::Call { args, .. } =
                                    &data.terminator.as_ref().unwrap().kind
                                else {
                                    unreachable!()
                                };
                                let Some(PlaceElem::Field(index, _)) =
                                    args[0].place().unwrap().projection.last()
                                else {
                                    panic!("Clone receives its component value")
                                };
                                let index = index.index();
                                indices.push(index);
                                assert!(matches!(
                                    body.basic_blocks[*failure]
                                        .terminator
                                        .as_ref()
                                        .unwrap()
                                        .kind,
                                    TerminatorKind::ResumeUnwind
                                ));
                                cursor = *target;
                            }
                            TerminatorKind::Return => break,
                            other => panic!("unexpected Clone control flow: {other:?}"),
                        }
                    }
                    assert_eq!(indices, [0, 1, 2]);
                }
            },
        );
    }
}
