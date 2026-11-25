//! Publish conformance-owned instance families without mutating the class's
//! defining package. Ordinary generated forwarders are checked after their
//! generic source defaults publish conditional class-receiver proofs.
use crate::{
    compile::context::Gcx,
    error::CompileResult,
    hir::{self, HirVisitor},
    sema::{
        models::{
            ClassAdoption, ClassMethod, ClassWitnessMethod, MethodImplementation, SelectionMode,
        },
        tycheck::utils::normalize_aliases,
    },
};
use rustc_hash::FxHashSet;

pub fn run<'ctx>(package: &hir::Package, gcx: Gcx<'ctx>) -> CompileResult<()> {
    struct SelfResults {
        methods: FxHashSet<hir::DefinitionID>,
        finals: FxHashSet<hir::DefinitionID>,
    }
    impl HirVisitor for SelfResults {
        fn visit_declaration(&mut self, node: &hir::Declaration) {
            if let hir::DeclarationKind::Impl(value) = &node.kind {
                for member in &value.declarations {
                    if let hir::AssociatedDeclarationKind::Function(function) = &member.kind
                        && function.is_final
                    {
                        self.finals.insert(member.id);
                    }
                    if let hir::AssociatedDeclarationKind::Function(function) = &member.kind
                        && function.signature.prototype.output.as_ref().is_some_and(|output|
                            matches!(&output.kind, hir::TypeKind::Nominal(hir::ResolvedPath::Resolved(path))
                                if matches!(path.resolution, hir::Resolution::SelfTypeAlias(_)))) {
                        self.methods.insert(member.id);
                    }
                }
            }
            hir::walk_declaration(self, node);
        }
    }
    let mut results = SelfResults {
        methods: FxHashSet::default(),
        finals: FxHashSet::default(),
    };
    hir::walk_package(&mut results, package);
    let mut records = gcx.all_conformance_records(gcx.package_index());
    // Publish ancestors first so partial overrides inherit concrete default
    // adapters as well as explicit bodies, independently of source order.
    records.sort_by_key(|record| {
        (
            record
                .interface
                .self_ty()
                .map_or(0, |class| gcx.class_ancestry(class).len()),
            record.extension,
        )
    });
    for record in records {
        let Some(class) = record.interface.self_ty() else {
            continue;
        };
        if !gcx.class_info(class).is_some_and(|info| !info.is_final) {
            continue;
        }
        let Some((conformance, _)) = gcx.with_session_type_database(|database| {
            database
                .conformance_records
                .iter()
                .find(|(_, candidate)| {
                    candidate.extension == record.extension
                        && candidate.interface == record.interface
                })
                .map(|(id, record)| (*id, *record))
        }) else {
            continue;
        };
        let mut assumptions: Vec<_> =
            crate::sema::tycheck::constraints::canonical_constraints_of(gcx, record.extension)
                .into_iter()
                .map(|constraint| constraint.value)
                .collect();
        if [hir::StdItem::Encodable, hir::StdItem::Decodable]
            .iter()
            .any(|item| gcx.std_item_def(*item) == Some(record.interface.id))
            && let Some(fields) = crate::sema::tycheck::derive::conditional_fields(gcx, record)
        {
            // Publish a conditional generic catalog under the same field
            // requirements that callers must prove at concrete instantiation.
            for ty in fields {
                assumptions.push(crate::sema::models::Constraint::Bound {
                    ty,
                    interface: crate::sema::models::InterfaceReference {
                        id: record.interface.id,
                        arguments: gcx.store.interners.intern_generic_args(vec![
                            crate::sema::models::GenericArgument::Type(ty),
                        ]),
                        bindings: &[],
                    },
                });
            }
        }
        let assumptions = gcx.store.arenas.global.alloc_slice_copy(&assumptions);
        let Some(goal) = record.interface.to_goal(gcx, assumptions) else {
            continue;
        };
        let Ok(witness) = gcx.build_conformance_witness(goal, SelectionMode::Typecheck) else {
            gcx.dcx().emit_error("non-final class conformance needs a complete checked witness before its virtual catalog can be published".into(), Some(record.location));
            continue;
        };
        let mut methods = vec![];
        let mut selected: Vec<_> = witness.method_witnesses.into_iter().collect();
        selected.sort_by_key(|(requirement, _)| *requirement);
        for (requirement, witness) in selected {
            let signature = gcx.get_signature(requirement);
            // Only the builtin Decodable factory is allowed nested Self here:
            // a checked required initializer family constructs the subclass.
            if gcx.std_item_def(hir::StdItem::Decodable) == Some(record.interface.id)
                && witness.implementation.impl_id().is_some_and(|id| {
                    matches!(
                        gcx.store
                            .synthetic_definitions
                            .borrow()
                            .get(&id)
                            .map(|value| value.kind),
                        Some(crate::sema::models::SyntheticDefinitionKind::ClassDecoder { .. })
                    )
                })
            {
                continue;
            }
            if !crate::sema::lowering::class_defaults::class_interface_signature_supported(
                gcx, signature,
            ) {
                gcx.dcx().emit_error("non-final class witnesses cannot adapt invariant, nested or borrowed Self storage; use a concrete interface argument or owned Self result".into(), Some(record.location));
                continue;
            }
            if !signature
                .inputs
                .first()
                .is_some_and(|input| gcx.symbol_text(input.name).as_str() == "self")
            {
                continue;
            }
            let returns_self =
                normalize_aliases(gcx, signature.output) == gcx.types.self_type_parameter;
            let (implementation, default) = match witness.implementation {
                MethodImplementation::Concrete(implementation) => (implementation, false),
                MethodImplementation::Synthetic(
                    crate::sema::models::SyntheticMethodKind::MemberwiseEncode,
                    Some(implementation),
                ) => (implementation, false),
                MethodImplementation::Default(source) => {
                    let Some(adapter) = gcx.adopted_class_default(conformance, source) else {
                        gcx.dcx().emit_error(
                            "cannot construct the class default's forwarding environment".into(),
                            Some(record.location),
                        );
                        continue;
                    };
                    (adapter, true)
                }
                _ => {
                    gcx.dcx().emit_error(
                        "non-final class synthesis requires an explicit implementation".into(),
                        Some(record.location),
                    );
                    continue;
                }
            };
            let existing = gcx.class_method(class, implementation);
            // An explicit subclass body replaces only this requirement's
            // inherited conformance family, never a same-named inherent one.
            let inherited = crate::sema::impl_engine::witness::inherited_class_witness(
                gcx,
                &record,
                crate::sema::models::GenericArguments::empty(),
            )
            .and_then(|witness| {
                let method = witness.method_witnesses.get(&requirement)?;
                gcx.class_method(gcx.class_base(class)?, method.implementation.impl_id()?)
            });
            if returns_self
                && !default
                && !results.methods.contains(&implementation)
                && !existing.is_some_and(|slot| slot.returns_self)
            {
                gcx.dcx().emit_error("a non-final class Self witness must declare an owned Self result preserving the actual subclass".into(), Some(gcx.definition_ident(implementation).span));
                continue;
            }
            methods.push(ClassWitnessMethod {
                requirement,
                slot: existing
                    .or_else(|| {
                        inherited.map(|slot| ClassMethod {
                            implementation,
                            owner: class,
                            is_final: results.finals.contains(&implementation),
                            ..slot
                        })
                    })
                    .unwrap_or(ClassMethod {
                        returns_self,
                        family: implementation,
                        implementation,
                        owner: class,
                        is_final: results.finals.contains(&implementation),
                    }),
                is_registered: existing
                    .is_some_and(|slot| gcx.class_family_is_registered(slot.family))
                    || inherited.is_some_and(|slot| gcx.class_family_is_registered(slot.family))
                    || existing.is_none(),
            });
        }
        gcx.with_session_type_database(|database| {
            database.selection_cache.clear();
            database.witness_cache.clear();
            database.class_adoptions.push(ClassAdoption {
                conformance,
                methods: gcx.store.arenas.global.alloc_slice_copy(&methods),
            })
        });
    }
    // Header selection may have happened before the effective catalog existed.
    gcx.with_session_type_database(|database| {
        database.selection_cache.clear();
        database.witness_cache.clear();
    });
    gcx.dcx().ok()
}

/// Catalog construction can turn a subclass's explicit implementation into an
/// override of an existing family. Reuse that family in every witness row.
pub(crate) fn refresh<'ctx>(gcx: Gcx<'ctx>) {
    let adoptions = gcx.with_session_type_database(|database| database.class_adoptions.clone());
    let refreshed: Vec<_> = adoptions
        .into_iter()
        .map(|adoption| {
            let record = gcx
                .conformance_record(adoption.conformance)
                .expect("local class adoption");
            let class = record.interface.self_ty().expect("class receiver");
            let methods: Vec<_> = adoption
                .methods
                .iter()
                .map(|method| {
                    let slot = gcx
                        .class_method(class, method.slot.implementation)
                        .unwrap_or(method.slot);
                    crate::sema::models::ClassWitnessMethod {
                        slot,
                        is_registered: (method.is_registered && slot.family == method.slot.family)
                            || gcx.class_family_is_registered(slot.family),
                        ..*method
                    }
                })
                .collect();
            ClassAdoption {
                methods: gcx.store.arenas.global.alloc_slice_copy(&methods),
                ..adoption
            }
        })
        .collect();
    gcx.with_session_type_database(|database| {
        database.class_adoptions = refreshed;
        database.selection_cache.clear();
        database.witness_cache.clear();
    });
}

#[cfg(test)]
mod tests {
    #[test]
    fn explicit_witnesses_cannot_strengthen_generic_requirements() {
        for (bound, valid) in [("", true), (": Marker", false)] {
            let source = format!(
                "interface Marker {{}}\ninterface Echo {{ func echo[T](_ value: T) -> T; }}\nclass Base {{}}\nconform Base to Echo {{ func echo[T{bound}](_ value: T) -> T {{ value }}; }}\nfunc main() {{}}"
            );
            let diagnostics = crate::test_support::analyze_script_diagnostics(&source);
            assert_eq!(diagnostics.is_empty(), valid, "{bound}: {diagnostics:#?}");
        }
    }

    #[test]
    fn adopted_generic_defaults_and_argument_providers_use_extension_coordinates() {
        crate::test_support::analyze_script_built_mir(
            r#"
interface Readable[A] {
    func choose[T](_ value: T, _ amount: int32 = 7) -> T { value }
    func read(_ input: &A) -> int32 { 7 }
}
class Box[U, V, W] {}
conform[W, V, U] Box[U, V, W] to Readable[int32] {}
func main() {}
"#,
            |mut bodies, gcx| {
                assert!(crate::mir::class_defaults::collect(gcx, bodies.iter()).is_ok());
                for body in &mut bodies {
                    crate::mir::optimize::run_local_passes(gcx, body)
                        .unwrap_or_else(|_| panic!("{:#?}", gcx.dcx().take_recorded_diagnostics()));
                }
                let database = gcx.with_session_type_database(|database| database.clone());
                let synthetics: Vec<_> = gcx
                    .store
                    .synthetic_definitions
                    .borrow()
                    .iter()
                    .map(|(id, value)| (*id, value.clone()))
                    .collect();
                let choose = synthetics
                    .iter()
                    .find(|(_, value)| gcx.symbol_text(value.name).as_str() == "choose")
                    .unwrap();
                assert_eq!(choose.1.generics.parent_count, 3);
                assert_eq!(choose.1.generics.parameters[0].index, 3);
                assert!(
                    choose
                        .1
                        .signature
                        .inputs
                        .last()
                        .unwrap()
                        .default_provider
                        .is_some()
                );
                let _ = database;
            },
        );
    }

    #[test]
    fn adopted_defaults_rebase_their_environment_and_inherited_override_family() {
        crate::test_support::analyze_script_built_mir(
            r#"
interface Readable {
    func read() -> int32 { 7 }
    func choose[T](_ value: &T) -> int32 { self.read() }
    func identity() -> Self { self }
    func step() {}
}
class Base: Readable { value: int32 }
class Derived: Base {}
conform Derived to Readable { override func read() -> int32 { 17 }; }
func main() {}
"#,
            |mut bodies, gcx| {
                assert!(crate::mir::class_defaults::collect(gcx, bodies.iter()).is_ok());
                for body in &mut bodies {
                    crate::mir::optimize::run_local_passes(gcx, body)
                        .unwrap_or_else(|_| panic!("{:#?}", gcx.dcx().take_recorded_diagnostics()));
                }
                let adapters: Vec<_> = gcx
                    .store
                    .synthetic_definitions
                    .borrow()
                    .iter()
                    .filter_map(|(id, definition)| {
                        matches!(
                            definition.kind,
                            crate::sema::models::SyntheticDefinitionKind::AdoptedClassDefault { .. }
                        )
                        .then_some(*id)
                    })
                    .collect();
                assert_eq!(adapters.len(), 4);
                for adapter in adapters {
                    let identity =
                        crate::sema::tycheck::utils::generics::GenericsBuilder::identity_for_item(
                            gcx, adapter,
                        );
                    let (source, arguments) =
                        gcx.adapter_source_arguments(adapter, identity).unwrap();
                    assert_eq!(
                        arguments.len(),
                        gcx.generics_of(source).parent_count
                            + gcx.generics_of(source).parameters.len()
                    );
                    assert!(bodies.iter().any(|body| body.owner == adapter));
                }
            },
        );
    }

    #[test]
    fn explicit_class_witnesses_share_virtual_families_with_subclass_overrides() {
        crate::test_support::analyze_script(
            r#"
interface Readable {
    func read() -> int32
    func step()
    func identity() -> Self
}
class Base { value: int32 }
conform Base to Readable {
    func read() -> int32 { self.value }
    func step() { self.value += 1 }
    func identity() -> Self { self }
}
class Derived: Base {}
conform Derived to Readable {
    override func read() -> int32 { super.read() + 10 }
    override func step() { super.step(); self.value += 1 }
}
func genericRead[T: Readable](_ value: &T) -> int32 { value.read() }
func check(_ value: &Derived) -> Derived {
    value.step()
    var count: int32 = genericRead(&*value)
    value.identity()
}
func main() {}
"#,
            |package, gcx| {
                let named = |name: &str| {
                    package
                        .root
                        .declarations
                        .iter()
                        .find(|declaration| gcx.symbol_text(declaration.identifier.symbol).as_str() == name)
                        .unwrap()
                        .id
                };
                let base = gcx.get_type(named("Base"));
                let derived = gcx.get_type(named("Derived"));
                for method in gcx.class_methods(base) {
                    assert!(gcx.class_family_is_registered(method.family));
                    let child = gcx.class_method(derived, method.family).unwrap();
                    if gcx.symbol_text(gcx.definition_ident(method.implementation).symbol).as_str() == "identity" {
                        assert!(child.returns_self);
                    } else {
                        assert_ne!(child.implementation, method.implementation);
                    }
                }
                assert_eq!(gcx.class_methods(base).len(), 3);
                let interface = named("Readable");
                let arguments = gcx
                    .store
                    .interners
                    .intern_generic_args(vec![crate::sema::models::GenericArgument::Type(derived)]);
                let reference = crate::sema::models::InterfaceReference {
                    id: interface,
                    arguments,
                    bindings: &[],
                };
                let witness = gcx
                    .build_conformance_witness(
                        reference.to_goal(gcx, &[]).unwrap(),
                        crate::sema::models::SelectionMode::Codegen,
                    )
                    .unwrap();
                assert_eq!(witness.method_witnesses.len(), 3);
            },
        );
    }

    #[test]
    fn nonfinal_class_witnesses_reject_unsafe_self_adaptation() {
        for (requirement, implementation, extra, diagnostic) in [
            (
                "func read(_ other: &Self)",
                "func read(_ other: &Self) {}",
                "",
                "invariant, nested or borrowed Self",
            ),
            (
                "func read() -> &Self",
                "func read() -> &Self { self }",
                "",
                "invariant, nested or borrowed Self",
            ),
            (
                "func read() -> Self",
                "func read() -> Base { *self }",
                "",
                "must declare an owned Self result",
            ),
        ] {
            let source = format!(
                "interface P {{ {requirement}; }}\nclass Base {{}}\n{extra}\nconform Base to P {{ {implementation}; }}\nfunc main() {{}}"
            );
            let diagnostics = crate::test_support::analyze_script_diagnostics(&source);
            assert!(
                diagnostics
                    .iter()
                    .any(|record| record.message.contains(diagnostic)),
                "{diagnostic}: {diagnostics:#?}"
            );
        }
    }
}
