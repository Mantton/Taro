use super::MirPass;
use super::simplify::{
    collapse_trivial_gotos, eliminate_dead_locals, merge_linear_blocks, prune_unreachable_blocks,
};
use crate::compile::context::Gcx;
use crate::error::CompileResult;
use crate::hir::DefinitionKind;
use crate::mir::{
    Body, LocalDecl, LocalKind, MirPhase, Operand, Place, PlaceElem, Rvalue, Statement,
    StatementKind,
};
use crate::sema::models::TyKind;
use crate::sema::tycheck::utils::instantiate::instantiate_ty_with_args;

pub struct SimplifyCfg;
pub struct PruneUnreachable;
pub struct LowerAggregates;
pub struct DeadLocalElimination;

impl<'ctx> MirPass<'ctx> for PruneUnreachable {
    fn name(&self) -> &'static str {
        "PruneUnreachable"
    }

    fn run(&mut self, _gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> CompileResult<()> {
        prune_unreachable_blocks(body);
        Ok(())
    }
}

impl<'ctx> MirPass<'ctx> for SimplifyCfg {
    fn name(&self) -> &'static str {
        "SimplifyCfg"
    }

    fn run(&mut self, _gcx: Gcx<'_>, body: &mut Body<'_>) -> CompileResult<()> {
        // 1. Merge linear chains of blocks (even with statements)
        merge_linear_blocks(body);
        // 2. Collapse remaining empty goto chains
        collapse_trivial_gotos(body);
        // 3. Remove now-unreachable blocks
        prune_unreachable_blocks(body);
        Ok(())
    }
}

impl<'ctx> MirPass<'ctx> for DeadLocalElimination {
    fn name(&self) -> &'static str {
        "DeadLocalElimination"
    }

    fn run(&mut self, _gcx: Gcx<'_>, body: &mut Body<'_>) -> CompileResult<()> {
        eliminate_dead_locals(body);
        Ok(())
    }
}

impl<'ctx> MirPass<'ctx> for LowerAggregates {
    fn name(&self) -> &'static str {
        "LowerAggregates"
    }

    fn run(&mut self, gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> CompileResult<()> {
        for bb in body.basic_blocks.indices() {
            let statements = std::mem::take(&mut body.basic_blocks[bb].statements);
            let mut lowered = Vec::with_capacity(statements.len());

            for stmt in statements {
                let span = stmt.span;
                let StatementKind::Assign(dest, Rvalue::Aggregate { kind, fields }) = stmt.kind
                else {
                    lowered.push(stmt);
                    continue;
                };
                // LLVM builds arrays and noncollecting enum constructors as
                // complete values. Other aggregates retain staged copies and
                // publish their tag only after all field stores below.
                if matches!(kind, crate::mir::AggregateKind::Array { .. })
                    || kind.noncollecting_enum_ctor(gcx).is_some()
                {
                    lowered.push(Statement {
                        kind: StatementKind::Assign(dest, Rvalue::Aggregate { kind, fields }),
                        span,
                    });
                    continue;
                }

                let mut field_base = dest.clone();
                let mut variant_index = None;
                let field_tys: Vec<_> = match kind {
                    crate::mir::AggregateKind::Tuple => {
                        let TyKind::Tuple(items) = body.place_ty(gcx, &dest).kind() else {
                            panic!("tuple aggregate must have a tuple destination");
                        };
                        items.to_vec()
                    }
                    crate::mir::AggregateKind::Adt {
                        def_id,
                        variant_index: variant,
                        generic_args,
                    } => match gcx.definition_kind(def_id) {
                        DefinitionKind::Struct => gcx
                            .get_struct_definition(def_id)
                            .fields
                            .iter()
                            .map(|field| instantiate_ty_with_args(gcx, field.ty, generic_args))
                            .collect(),
                        DefinitionKind::Enum => {
                            let index = variant.expect("enum aggregate variant");
                            let variant = gcx.enum_variant_by_index(def_id, index);
                            field_base.projection.push(PlaceElem::VariantDowncast {
                                name: variant.name,
                                index,
                            });
                            variant_index = Some(index);
                            fields
                                .iter()
                                .map(|operand| body.operand_ty(gcx, operand))
                                .collect()
                        }
                        _ => unreachable!("aggregate must be a struct or enum"),
                    },
                    crate::mir::AggregateKind::Closure {
                        def_id,
                        captured_generics,
                    } => gcx
                        .get_closure_captures(def_id)
                        .map(|info| {
                            info.captures
                                .iter()
                                .map(|capture| capture.storage_ty(gcx, captured_generics))
                                .collect()
                        })
                        .unwrap_or_default(),
                    crate::mir::AggregateKind::Array { .. } => unreachable!(),
                };
                assert_eq!(fields.len(), field_tys.len(), "aggregate field count");

                // Read every operand before writing any destination field: the
                // destination may overlap an input (for example a tuple swap).
                let mut temps = Vec::with_capacity(fields.len());
                for ((index, operand), field_ty) in fields.into_iter_enumerated().zip(field_tys) {
                    let ty = body.operand_ty(gcx, &operand);
                    let local = body.locals.push(LocalDecl {
                        ty,
                        kind: LocalKind::Temp,
                        mutable: true,
                        name: None,
                        span,
                    });
                    // An erased payload copy may collect. Finish every owned
                    // snapshot before transferring fields into a not-yet-
                    // published enum variant; otherwise earlier fields can
                    // become unreachable while its tag still names .empty.
                    let snapshot = match operand {
                        Operand::Copy(source) => Rvalue::CopyValue { source },
                        operand => Rvalue::Use(operand),
                    };
                    lowered.push(Statement {
                        kind: StatementKind::Assign(Place::from_local(local), snapshot),
                        span,
                    });
                    temps.push((local, index, field_ty));
                }
                for (local, index, field_ty) in temps {
                    let mut place = field_base.clone();
                    place.projection.push(PlaceElem::Field(index, field_ty));
                    lowered.push(Statement {
                        kind: StatementKind::Assign(
                            place,
                            // This temporary already owns its independent
                            // snapshot and has exactly this one consumer. A
                            // construction transfer must not clone it again.
                            Rvalue::Use(Operand::copy_with(
                                Place::from_local(local),
                                crate::mir::CopyModifiers { init: true },
                            )),
                        ),
                        span,
                    });
                }

                if let Some(variant_index) = variant_index {
                    // Publish the tag only after all payload stores. A tag-aware
                    // collector must never observe stale payload storage.
                    lowered.push(Statement {
                        kind: StatementKind::SetDiscriminant {
                            place: dest,
                            variant_index,
                        },
                        span,
                    });
                } else if dest.projection.is_empty() {
                    // This safepoint-free store sequence has initialized the
                    // whole local, even when the aggregate has no fields.
                    lowered.push(Statement {
                        kind: StatementKind::SetInitialized(dest.local),
                        span,
                    });
                }
            }
            body.basic_blocks[bb].statements = lowered;
        }
        Ok(())
    }

    fn phase_change(&self) -> Option<MirPhase> {
        Some(MirPhase::Lowered)
    }
}

#[cfg(test)]
mod tests {
    use super::LowerAggregates;
    use crate::{
        PackageIndex,
        hir::{DefinitionID, NodeID},
        mir::{
            AggregateKind, Operand, Place, PlaceElem, Rvalue, Statement, StatementKind,
            optimize::MirPass,
            test_support::{minimal_body, push_temp, with_test_gcx},
        },
        sema::{
            models::{
                CaptureKind, CapturedVar, ClosureCaptures, ClosureKind, GenericArgument,
                GenericParameter, Ty, TyKind,
            },
            resolve::models::DefinitionIndex,
        },
        span::{FileID, Span},
        thir::FieldIndex,
    };

    #[test]
    fn aggregate_lowering_reads_overlapping_fields_before_writing() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let ty = Ty::new(
                TyKind::Tuple(gcx.store.interners.intern_ty_list(vec![gcx.types.int32; 2])),
                gcx,
            );
            let local = push_temp(&mut body, ty);
            let span = body.locals[local].span;
            let field = |index| Place {
                local,
                projection: vec![PlaceElem::Field(
                    FieldIndex::from_raw(index),
                    gcx.types.int32,
                )],
            };
            body.basic_blocks[body.start_block]
                .statements
                .push(Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(local),
                        Rvalue::Aggregate {
                            kind: AggregateKind::Tuple,
                            fields: vec![
                                Operand::Copy(field(1)),
                                Operand::CopyWith(
                                    field(0),
                                    crate::mir::CopyModifiers { init: true },
                                ),
                            ]
                            .into_iter()
                            .collect(),
                        },
                    ),
                    span,
                });

            assert!(LowerAggregates.run(gcx, &mut body).is_ok());

            let statements = &body.basic_blocks[body.start_block].statements;
            assert_eq!(statements.len(), 5);
            assert!(
                matches!(&statements[0].kind, StatementKind::Assign(dest, Rvalue::CopyValue { source }) if dest.local != local && source == &field(1))
            );
            assert!(
                matches!(&statements[1].kind, StatementKind::Assign(dest, Rvalue::Use(Operand::CopyWith(source, modifiers))) if dest.local != local && source == &field(0) && modifiers.init)
            );
            for (index, statement) in statements[2..4].iter().enumerate() {
                assert!(
                    matches!(&statement.kind, StatementKind::Assign(dest, Rvalue::Use(Operand::CopyWith(source, modifiers))) if dest == &field(index as u32) && source.projection.is_empty() && modifiers.init)
                );
            }
            assert!(matches!(statements[4].kind, StatementKind::SetInitialized(id) if id == local));
            crate::mir::gc_lowering::lower_for_gc(&mut body);
            assert!(body.basic_blocks[body.start_block].statements[2..4].iter().all(|statement| {
                matches!(statement.kind, StatementKind::Assign(_, Rvalue::Use(Operand::CopyWith(_, modifiers))) if modifiers.init)
            }), "field transfers must remain noncollecting after GC normalization");
        });
    }

    #[test]
    fn enum_payload_aggregate_uses_instantiated_field_types() {
        use crate::sema::models::{
            AdtDef, AdtKind, EnumDefinition, EnumVariant, EnumVariantField, EnumVariantKind,
        };
        use crate::thir::VariantIndex;

        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let enum_id = DefinitionID::new(PackageIndex::new(1), DefinitionIndex::from_raw(10));
            let adt_def = AdtDef {
                kind: AdtKind::Enum,
                id: enum_id,
            };
            let parameter = Ty::new(
                TyKind::Parameter(GenericParameter {
                    index: 0,
                    name: gcx.intern_symbol("T"),
                }),
                gcx,
            );
            let name = gcx.intern_symbol("Some");
            let fields = gcx
                .store
                .arenas
                .global
                .alloc_slice_copy(&[EnumVariantField {
                    label: None,
                    ty: parameter,
                    mutability: crate::hir::Mutability::Mutable,
                }]);
            let variants = gcx.store.arenas.global.alloc_slice_copy(&[EnumVariant {
                name,
                def_id: enum_id,
                ctor_def_id: enum_id,
                kind: EnumVariantKind::Tuple(fields),
                discriminant: 0,
            }]);
            gcx.cache_enum_definition(enum_id, EnumDefinition { adt_def, variants });
            let args = gcx
                .store
                .interners
                .intern_generic_args(vec![GenericArgument::Type(gcx.types.int32)]);
            let destination = push_temp(&mut body, Ty::new(TyKind::Adt(adt_def, args), gcx));
            let value = push_temp(&mut body, gcx.types.int32);
            let span = body.locals[destination].span;
            body.basic_blocks[body.start_block]
                .statements
                .push(Statement {
                    kind: StatementKind::Assign(
                        Place {
                            local: destination,
                            projection: vec![PlaceElem::VariantDowncast {
                                name,
                                index: VariantIndex::from_raw(0),
                            }],
                        },
                        Rvalue::Aggregate {
                            kind: AggregateKind::Tuple,
                            fields: vec![Operand::Copy(Place::from_local(value))]
                                .into_iter()
                                .collect(),
                        },
                    ),
                    span,
                });

            assert!(LowerAggregates.run(gcx, &mut body).is_ok());

            let StatementKind::Assign(destination, _) =
                &body.basic_blocks[body.start_block].statements[1].kind
            else {
                panic!("expected payload field assignment");
            };
            assert_eq!(
                destination.projection.last(),
                Some(&PlaceElem::Field(FieldIndex::from_raw(0), gcx.types.int32))
            );
        });
    }

    #[test]
    fn closure_aggregate_fields_use_captured_generic_arguments() {
        for capture_kind in [CaptureKind::ByCopy, CaptureKind::ByRef] {
            with_test_gcx(|gcx| {
                let mut body = minimal_body(gcx);
                let span = Span::empty(FileID::new(0));
                let closure_id =
                    DefinitionID::new(PackageIndex::new(1), DefinitionIndex::from_raw(10));
                let parameter = Ty::new(
                    TyKind::Parameter(GenericParameter {
                        index: 0,
                        name: gcx.intern_symbol("T"),
                    }),
                    gcx,
                );
                gcx.cache_closure_captures(
                    closure_id,
                    ClosureCaptures {
                        captures: vec![CapturedVar {
                            source_id: NodeID::from_raw(0),
                            root_ty: parameter,
                            projection: &[],
                            name: gcx.intern_symbol("value"),
                            ty: parameter,
                            capture_kind,
                            source_immutable: false,
                            field_index: FieldIndex::from_raw(0),
                        }],
                        kind: ClosureKind::Fn,
                    },
                );

                let captured_generics = gcx
                    .store
                    .interners
                    .intern_generic_args(vec![GenericArgument::Type(gcx.types.int32)]);
                let closure_ty = Ty::new(
                    TyKind::Closure {
                        closure_def_id: closure_id,
                        kind: ClosureKind::Fn,
                        captured_generics,
                        inputs: gcx.store.interners.intern_ty_list(Vec::new()),
                        output: gcx.types.void,
                    },
                    gcx,
                );
                let destination = push_temp(&mut body, closure_ty);
                let storage_ty = match capture_kind {
                    CaptureKind::ByRef => Ty::new(TyKind::Reference(gcx.types.int32), gcx),
                    _ => gcx.types.int32,
                };
                let value = push_temp(&mut body, storage_ty);
                body.basic_blocks[body.start_block]
                    .statements
                    .push(Statement {
                        kind: StatementKind::Assign(
                            Place::from_local(destination),
                            Rvalue::Aggregate {
                                kind: AggregateKind::Closure {
                                    def_id: closure_id,
                                    captured_generics,
                                },
                                fields: vec![Operand::copy(Place::from_local(value))]
                                    .into_iter()
                                    .collect(),
                            },
                        ),
                        span,
                    });

                assert!(LowerAggregates.run(gcx, &mut body).is_ok());

                assert!(matches!(
                    body.basic_blocks[body.start_block]
                        .statements
                        .last()
                        .map(|statement| &statement.kind),
                    Some(StatementKind::SetInitialized(local)) if *local == destination
                ));

                let field_ty = body.basic_blocks[body.start_block]
                    .statements
                    .iter()
                    .find_map(|statement| match &statement.kind {
                        StatementKind::Assign(place, _)
                            if place.local == destination && !place.projection.is_empty() =>
                        {
                            match place.projection.last() {
                                Some(PlaceElem::Field(_, ty)) => Some(*ty),
                                _ => None,
                            }
                        }
                        _ => None,
                    })
                    .expect("lowered closure field assignment");
                assert_eq!(field_ty, storage_ty);
            });
        }
    }

    #[test]
    fn empty_aggregate_still_publishes_initialization() {
        with_test_gcx(|gcx| {
            let mut body = minimal_body(gcx);
            let span = body.locals[body.return_local].span;
            let tuple_ty = Ty::new(
                TyKind::Tuple(gcx.store.interners.intern_ty_list(Vec::new())),
                gcx,
            );
            let destination = push_temp(&mut body, tuple_ty);
            body.basic_blocks[body.start_block]
                .statements
                .push(Statement {
                    kind: StatementKind::Assign(
                        Place::from_local(destination),
                        Rvalue::Aggregate {
                            kind: AggregateKind::Tuple,
                            fields: Vec::new().into_iter().collect(),
                        },
                    ),
                    span,
                });

            assert!(LowerAggregates.run(gcx, &mut body).is_ok());
            assert!(matches!(
                body.basic_blocks[body.start_block].statements.as_slice(),
                [Statement {
                    kind: StatementKind::SetInitialized(local),
                    ..
                }] if *local == destination
            ));
        });
    }
}
