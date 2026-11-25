//! Intrinsic Clone whose specified operation is a Copy. The generic declaration
//! is shared; its MIR is built per concrete instance, never per tuple arity or
//! reference head. Reusing one concrete body for two layouts corrupts values.
use crate::{
    compile::context::Gcx,
    error::{CompileResult, ReportedError},
    hir::DefinitionID,
    mir::{
        BasicBlockData, Body, LocalDecl, LocalKind, MirPhase, Operand, Place, PlaceElem, Rvalue,
        Statement, StatementKind, Terminator, TerminatorKind,
    },
    sema::{
        models::{
            GenericArgument, GenericParameter, GenericParameterDefinition,
            GenericParameterDefinitionKind, Generics, LabeledFunctionParameter,
            LabeledFunctionSignature, SyntheticDefinition, SyntheticDefinitionKind, Ty, TyKind,
        },
        tycheck::utils::{normalize_post_monomorphization, unresolved::storage_needs_substitution},
    },
    span::Span,
    specialize::Instance,
};
use index_vec::IndexVec;
mod elements;

pub fn declaration(gcx: Gcx<'_>, span: Span) -> DefinitionID {
    declaration_with_kind(gcx, span, SyntheticDefinitionKind::BuiltinCopyClone)
}

pub(crate) fn declaration_with_kind(
    gcx: Gcx<'_>,
    span: Span,
    kind: SyntheticDefinitionKind,
) -> DefinitionID {
    assert!(kind.is_builtin_clone());
    let existing = gcx
        .store
        .synthetic_definitions
        .borrow()
        .iter()
        .find_map(|(id, definition)| {
            (id.package() == gcx.package_index() && definition.kind == kind).then_some(*id)
        });
    if let Some(id) = existing {
        return id;
    }
    let id = gcx.allocate_synthetic_id(gcx.package_index());
    let parameter_id = gcx.allocate_synthetic_id(gcx.package_index());
    let name = gcx.intern_symbol("T");
    let parameter = Ty::new(TyKind::Parameter(GenericParameter { index: 0, name }), gcx);
    let generics = gcx.store.arenas.generics.alloc(Generics {
        parameters: vec![GenericParameterDefinition {
            is_anonymous: false,
            name,
            id: parameter_id,
            index: 0,
            kind: GenericParameterDefinitionKind::Type { default: None },
        }],
        has_self: false,
        parent: None,
        parent_count: 0,
    });
    let signature = gcx
        .store
        .arenas
        .function_signatures
        .alloc(LabeledFunctionSignature {
            inputs: vec![LabeledFunctionParameter {
                name: gcx.intern_symbol("value"),
                label: None,
                is_lazy: false,
                default_provider: None,
                ty: parameter,
            }],
            output: parameter,
            is_variadic: false,
            abi: None,
        });
    gcx.register_synthetic_definition(
        id,
        SyntheticDefinition {
            kind,
            name: gcx.intern_symbol(match kind {
                SyntheticDefinitionKind::TupleClone => "$tupleClone",
                SyntheticDefinitionKind::ArrayClone => "$arrayClone",
                SyntheticDefinitionKind::ClosureClone => "$closureClone",

                _ => "$builtinCopyClone",
            }),
            generics,
            signature,
            span,
        },
    );
    gcx.cache_type(id, Ty::from_labeled_signature(gcx, signature));
    id
}

pub fn validate_declaration(definition: &SyntheticDefinition<'_>) -> Result<(), &'static str> {
    if !definition.kind.is_builtin_clone() {
        return Ok(());
    }
    let generics = definition.generics;
    if generics.parameters.len() != 1
        || generics.has_self
        || generics.parent.is_some()
        || generics.parent_count != 0
    {
        return Err("builtin Clone metadata has invalid generics");
    }
    let parameter = &generics.parameters[0];
    if parameter.index != 0
        || !matches!(
            &parameter.kind,
            GenericParameterDefinitionKind::Type { default: None }
        )
    {
        return Err("builtin Clone metadata must accept one type parameter");
    }
    let signature = definition.signature;
    let is_parameter = |ty: Ty<'_>| {
        matches!(ty.kind(), TyKind::Parameter(formal)
        if formal.index == 0 && formal.name == parameter.name)
    };
    if signature.abi.is_some()
        || signature.is_variadic
        || signature.inputs.len() != 1
        || !is_parameter(signature.output)
    {
        return Err("builtin Clone metadata has invalid ABI");
    }
    let input = &signature.inputs[0];
    if input.label.is_some() || input.default_provider.is_some() || !is_parameter(input.ty) {
        return Err("builtin Clone metadata must accept its result type by value");
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
    validate_declaration(&definition).map_err(error)?;
    if !definition.kind.is_builtin_clone() {
        return Err(error("incorrect generated Clone definition kind"));
    }
    let [GenericArgument::Type(ty)] = &instance.args[..] else {
        return Err(error("builtin Clone requires exactly one type argument"));
    };
    let ty = normalize_post_monomorphization(gcx, *ty);
    if storage_needs_substitution(gcx, ty) {
        return Err(error("builtin Clone requires a concrete type"));
    }
    if matches!(
        definition.kind,
        SyntheticDefinitionKind::TupleClone
            | SyntheticDefinitionKind::ArrayClone
            | SyntheticDefinitionKind::ClosureClone
    ) {
        if !matches!(
            (definition.kind, ty.kind()),
            (SyntheticDefinitionKind::TupleClone, TyKind::Tuple(_))
                | (SyntheticDefinitionKind::ArrayClone, TyKind::Array { .. })
                | (
                    SyntheticDefinitionKind::ClosureClone,
                    TyKind::Closure { .. }
                )
        ) {
            return Err(error(
                "generated Clone type does not match its representation family",
            ));
        }
        let body = elements::build_body(gcx, owner, ty, span)?;
        return Ok(body);
    }
    if !crate::sema::impl_engine::builtin_copy_clone(gcx, ty) {
        return Err(error(
            "builtin Clone requires a concrete intrinsic Copy representation",
        ));
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
        name: Some(gcx.intern_symbol("value")),
        span,
    });
    let mut basic_blocks = IndexVec::new();
    let uninhabited = matches!(ty.kind(), TyKind::Never);
    let start_block = basic_blocks.push(BasicBlockData {
        note: Some("concrete intrinsic Clone".into()),
        statements: if uninhabited {
            vec![]
        } else {
            vec![Statement {
                kind: StatementKind::Assign(
                    Place::from_local(return_local),
                    Rvalue::CopyValue {
                        source: Place {
                            local: parameter,
                            projection: vec![],
                        },
                    },
                ),
                span,
            }]
        },
        terminator: Some(Terminator {
            span,
            kind: if uninhabited {
                TerminatorKind::Unreachable
            } else {
                TerminatorKind::Return
            },
        }),
    });
    let body = Body {
        escape_locals: Vec::new(),

        owner,
        source_scopes: Body::initial_source_scopes(owner),
        locals,
        basic_blocks,
        start_block,
        return_local,
        phase: MirPhase::CfgClean,
        is_async: false,
        generator_element_ty: None,
    };
    Ok(body)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        span::{FileID, Span},
        test_support::with_test_gcx,
    };

    #[test]
    fn full_type_arguments_select_distinct_concrete_layouts() {
        with_test_gcx(|gcx| {
            let id = declaration(gcx, Span::empty(FileID::from_usize(0)));
            let small = Ty::new(
                TyKind::Tuple(
                    gcx.store
                        .interners
                        .intern_ty_list(vec![gcx.types.int32, gcx.types.int32]),
                ),
                gcx,
            );
            let large = Ty::new(
                TyKind::Tuple(
                    gcx.store
                        .interners
                        .intern_ty_list(vec![gcx.types.int64, gcx.types.string]),
                ),
                gcx,
            );
            for ty in [small, large] {
                let args = gcx
                    .store
                    .interners
                    .intern_generic_args(vec![GenericArgument::Type(ty)]);
                let instance = Instance::item(id, args);
                let body = gcx
                    .get_instance_mir_body(instance)
                    .ok()
                    .expect("concrete Clone MIR");
                assert_eq!(body.locals[body.return_local].ty, ty);
                assert!(gcx.is_finalized_instance_mir(instance, body));
            }
            assert!(
                gcx.store
                    .mir_packages
                    .borrow()
                    .values()
                    .all(|package| !package.functions.contains_key(&id))
            );
        });
    }

    #[test]
    fn generated_kind_and_signature_survive_metadata_and_reject_wrong_abi() {
        with_test_gcx(|gcx| {
            for kind in [
                SyntheticDefinitionKind::BuiltinCopyClone,
                SyntheticDefinitionKind::TupleClone,
                SyntheticDefinitionKind::ArrayClone,
                SyntheticDefinitionKind::ClosureClone,
            ] {
                let id = declaration_with_kind(gcx, Span::empty(FileID::from_usize(0)), kind);
                let definition = gcx
                    .store
                    .synthetic_definitions
                    .borrow()
                    .get(&id)
                    .unwrap()
                    .clone();
                let wire = crate::metadata::wire::synthetic_definition_to_wire(gcx.interner(), id, &definition);
                let bytes = bincode::serialize(&wire).unwrap();
                let restored = bincode::deserialize(&bytes).unwrap();
                let files = rustc_hash::FxHashMap::default();
                let (restored_id, decoded) = crate::metadata::wire::synthetic_definition_from_wire(
                    gcx,
                    &restored,
                    crate::metadata::wire::FileRemap { old_to_new: &files },
                );
                assert_eq!(restored_id, id);
                assert_eq!(decoded.kind, kind);
                assert!(validate_declaration(&decoded).is_ok());
                let mut invalid = decoded.clone();
                let mut signature = invalid.signature.clone();
                signature.output = gcx.types.bool;
                invalid.signature = gcx.store.arenas.function_signatures.alloc(signature);
                assert!(validate_declaration(&invalid).is_err());
            }
        });
    }

    #[test]
    fn materialization_does_not_turn_an_owned_nominal_type_into_copy() {
        crate::test_support::analyze_script(
            "struct Owned { value: int32 }\nfunc main() {}",
            |package, gcx| {
                let ty = gcx.get_type(package.root.declarations[0].id);
                let id = declaration(gcx, package.root.declarations[0].span);
                let args = gcx
                    .store
                    .interners
                    .intern_generic_args(vec![GenericArgument::Type(ty)]);
                assert!(build_body(gcx, Instance::item(id, args)).is_err());
            },
        );
    }
    #[test]
    fn concrete_instance_validation_rejects_wrong_parameters_and_missing_result() {
        for corrupt_parameters in [true, false] {
            with_test_gcx(|gcx| {
                let id = declaration(gcx, Span::empty(FileID::from_usize(0)));
                let args = gcx
                    .store
                    .interners
                    .intern_generic_args(vec![GenericArgument::Type(gcx.types.int32)]);
                let instance = Instance::item(id, args);
                let mut body = build_body(gcx, instance).ok().expect("copy body");
                if corrupt_parameters {
                    let parameter = body
                        .locals
                        .iter_mut()
                        .find(|local| local.kind == LocalKind::Param)
                        .unwrap();
                    parameter.ty = gcx.types.bool;
                } else {
                    body.basic_blocks[body.start_block].statements.clear();
                }
                assert!(
                    crate::mir::optimize::validate::validate_generated_instance_body(
                        gcx, instance, &body
                    )
                    .is_err()
                );
            });
        }
    }
}
