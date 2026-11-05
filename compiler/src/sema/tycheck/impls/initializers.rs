//! Constructor-family matching is distinct from instance-method overriding:
//! results name different classes, and matching a convenience entry alone does
//! not establish a designated-initializer override contract.
use crate::{
    compile::context::Gcx,
    error::CompileResult,
    hir::{self, HirVisitor},
    sema::{
        models::{GenericArguments, GenericParameterDefinitionKind, Ty, TyKind},
        tycheck::utils::{
            generics::GenericsBuilder,
            instantiate::{instantiate_constraint_with_args, instantiate_ty_with_args},
            normalize_aliases,
        },
    },
};
use rustc_hash::{FxHashMap, FxHashSet};

pub fn run(package: &hir::Package, gcx: Gcx<'_>) -> CompileResult<()> {
    struct Collector {
        classes: Vec<hir::DefinitionID>,
        overrides: FxHashMap<hir::DefinitionID, bool>,
        required: FxHashSet<hir::DefinitionID>,
    }
    impl HirVisitor for Collector {
        fn visit_declaration(&mut self, node: &hir::Declaration) {
            if let hir::DeclarationKind::Struct(value) = &node.kind
                && value.class_header.is_some()
            {
                self.classes.push(node.id);
            }
            hir::walk_declaration(self, node);
        }
        fn visit_assoc_declaration(
            &mut self,
            node: &hir::AssociatedDeclaration,
            context: hir::AssocContext,
        ) {
            if let hir::AssociatedDeclarationKind::Initializer(function) = &node.kind {
                self.overrides.insert(node.id, function.is_override);
                if function
                    .initializer_kind
                    .is_some_and(|kind| kind.is_required)
                {
                    self.required.insert(node.id);
                }
            }
            hir::walk_assoc_declaration(self, node, context);
        }
    }
    let mut collector = Collector {
        classes: vec![],
        overrides: FxHashMap::default(),
        required: FxHashSet::default(),
    };
    hir::walk_package(&mut collector, package);
    // Struct initializers have no inheritance contract to override.
    for (&id, &is_override) in &collector.overrides {
        let class = gcx
            .definition_parent(id)
            .and_then(|parent| gcx.get_impl_target_ty(parent));
        if is_override && class.is_none_or(|target| !gcx.is_class_type(target)) {
            gcx.dcx().emit_error(
                "override init requires a class designated-initializer contract".into(),
                Some(gcx.definition_ident(id).span),
            );
        }
        if collector.required.contains(&id) && class.is_none_or(|target| !gcx.is_class_type(target))
        {
            gcx.dcx().emit_error(
                "required init requires a class".into(),
                Some(gcx.definition_ident(id).span),
            );
        }
    }
    fn build<'ctx>(
        gcx: Gcx<'ctx>,
        class: Ty<'ctx>,
        overrides: &FxHashMap<hir::DefinitionID, bool>,
        done: &mut FxHashSet<hir::DefinitionID>,
    ) {
        let TyKind::Adt(def, _) = class.kind() else {
            return;
        };
        if !done.insert(def.id) {
            return;
        }
        let base = gcx.class_base(class);
        if let Some(base) = base
            && let TyKind::Adt(base_def, _) = base.kind()
            && base_def.id.package() == gcx.package_index()
        {
            build(gcx, gcx.get_type(base_def.id), overrides, done);
        }
        let mut definition = gcx.get_struct_definition(def.id).clone();
        let info = definition.class_info.as_mut().unwrap();
        let mut entries = info.initializers.to_vec();
        for initializer in &mut entries {
            let is_override = overrides
                .get(&initializer.definition)
                .copied()
                .unwrap_or(false);
            let span = gcx.definition_ident(initializer.definition).span;
            // Match in the extension's declared coordinates. A specialized
            // Child[Box[U]] initializer cannot be matched against abstract
            // Child[T] before the extension has supplied T's shape.
            let declared_class = gcx.initializer_target(initializer.definition);
            let declared_base = gcx.class_base(declared_class);
            let candidates: Vec<_> = declared_base
                .into_iter()
                .flat_map(|base| {
                    let TyKind::Adt(_, args) = base.kind() else {
                        unreachable!()
                    };
                    gcx.class_info(base)
                        .unwrap()
                        .initializers
                        .iter()
                        .filter(|entry| {
                            (!entry.is_convenience || entry.is_required)
                                && gcx.is_definition_visible(entry.definition, def.id)
                        })
                        .filter_map(|entry| {
                            let owner = instantiate_ty_with_args(gcx, entry.owner, args);
                            same_signature(
                                gcx,
                                declared_class,
                                initializer.definition,
                                owner,
                                entry.implementation,
                            )
                            .map(|arguments| (*entry, owner, arguments))
                        })
                        .collect::<Vec<_>>()
                })
                .collect();
            if candidates.len() > 1 {
                gcx.dcx().emit_error(
                    "initializer override is ambiguous between base designated signatures".into(),
                    Some(span),
                );
                continue;
            }
            let Some((inherited, _owner, (actual_args, base_args))) = candidates.first().copied()
            else {
                if is_override {
                    gcx.dcx().emit_error(
                        "override init has no matching base designated initializer".into(),
                        Some(span),
                    );
                }
                continue;
            };
            if !inherited.is_convenience && !is_override {
                gcx.dcx().emit_error(
                    "matching a base designated initializer requires override init".into(),
                    Some(span),
                );
            }
            if inherited.is_convenience && is_override {
                gcx.dcx().emit_error(
                    "matching a required convenience initializer uses required, not override"
                        .into(),
                    Some(span),
                );
            }
            // Constructor families retain the same Result error ABI. Only
            // their successful class handle is refined for a subclass.
            let actual_output = instantiate_ty_with_args(
                gcx,
                gcx.get_signature(initializer.definition).output,
                actual_args,
            );
            let base_output = instantiate_ty_with_args(
                gcx,
                gcx.get_signature(inherited.implementation).output,
                base_args,
            );
            if gcx
                .result_parts(actual_output)
                .map(|(_, error)| normalize_aliases(gcx, error))
                != gcx
                    .result_parts(base_output)
                    .map(|(_, error)| normalize_aliases(gcx, error))
            {
                gcx.dcx().emit_error(
                    "overriding init must preserve the base initializer's Result error type".into(),
                    Some(span),
                );
            }
            let constraints = |id, args| {
                gcx.constraints_of(id)
                    .into_iter()
                    .map(|constraint| {
                        normalize_aliases(
                            gcx,
                            instantiate_constraint_with_args(gcx, constraint.value, args),
                        )
                    })
                    .collect::<FxHashSet<_>>()
            };
            if constraints(initializer.definition, actual_args)
                != constraints(inherited.implementation, base_args)
            {
                gcx.dcx().emit_error("initializer override generic constraints must match the base after parameter renaming".into(), Some(span));
            }
            if gcx.definition_visibility(inherited.definition)
                == crate::sema::resolve::models::Visibility::Public
                && gcx.definition_visibility(initializer.definition)
                    != crate::sema::resolve::models::Visibility::Public
            {
                gcx.dcx().emit_error(
                    "an override of a public initializer must remain public".into(),
                    Some(span),
                );
            }
            if inherited.is_required && !initializer.is_required {
                gcx.dcx().emit_error(
                    "an explicit override of required init must repeat required".into(),
                    Some(span),
                );
            }
            initializer.family = inherited.family;
        }
        // Swift-style automatic designated inheritance is conditional on
        // defaults for this level's fields and no designated declaration here.
        if let Some(base) = base {
            let TyKind::Adt(base_def, _) = base.kind() else {
                unreachable!()
            };
            let inherited_fields = gcx.get_struct_definition(base_def.id).fields.len();
            if entries.iter().all(|entry| entry.is_convenience)
                && definition.fields[inherited_fields..]
                    .iter()
                    .all(|field| field.default_provider.is_some())
            {
                for entry in gcx
                    .class_info(base)
                    .unwrap()
                    .initializers
                    .iter()
                    // Inaccessible signatures still need hidden concrete
                    // entries for an inherited convenience body's delegation.
                    // Their original visibility is preserved by synthesis.
                    .filter(|entry| !entry.is_convenience)
                {
                    if entries
                        .iter()
                        .any(|existing| existing.family == entry.family)
                    {
                        continue;
                    }
                    if let Some(inherited) = inherit_designated(gcx, class, base, *entry) {
                        entries.push(inherited);
                    }
                }
            }
        }
        if let Some(base) = base {
            let TyKind::Adt(base_def, base_args) = base.kind() else {
                unreachable!()
            };
            let inherited_fields = gcx.get_struct_definition(base_def.id).fields.len();
            let base_entries = gcx.class_info(base).unwrap().initializers;
            let all_defaults = definition.fields[inherited_fields..]
                .iter()
                .all(|field| field.default_provider.is_some());
            let all_designated = base_entries
                .iter()
                .filter(|entry| !entry.is_convenience)
                .all(|base| entries.iter().any(|entry| entry.family == base.family));
            if all_defaults && all_designated {
                for entry in base_entries.iter().filter(|entry| {
                    entry.is_convenience && gcx.is_definition_visible(entry.definition, def.id)
                }) {
                    let owner = instantiate_ty_with_args(gcx, entry.owner, base_args);
                    if entries.iter().any(|existing| {
                        same_signature(gcx, class, existing.definition, owner, entry.implementation)
                            .is_some()
                    }) {
                        continue;
                    }
                    if let Some(inherited) = inherit_designated(gcx, class, base, *entry) {
                        entries.push(inherited);
                    }
                }
            }
        }
        if let Some(base) = base {
            for required in gcx
                .class_info(base)
                .unwrap()
                .initializers
                .iter()
                .filter(|entry| entry.is_required)
            {
                if !entries
                    .iter()
                    .any(|entry| entry.family == required.family && entry.is_required)
                {
                    gcx.dcx().emit_error(
                        "subclass must inherit or implement every required initializer".into(),
                        Some(gcx.definition_ident(def.id).span),
                    );
                }
            }
        }
        if !info.is_final {
            for entry in entries.iter().filter(|entry| entry.is_required) {
                if !gcx
                    .definition_visibility(entry.definition)
                    .supports_required_initializer(gcx.definition_visibility(def.id))
                {
                    gcx.dcx().emit_error(
                        "required initializer must be at least as visible as its non-final class"
                            .into(),
                        Some(gcx.definition_ident(def.id).span),
                    );
                }
            }
        }
        info.initializers = gcx.store.arenas.global.alloc_slice_copy(&entries);
        definition.has_initializer |= !entries.is_empty();
        gcx.cache_struct_definition(def.id, definition);
        for entry in entries.iter().filter(|entry| entry.is_inherited) {
            gcx.class_payload_initializer(entry.definition);
        }
    }
    let mut done = FxHashSet::default();
    for id in collector.classes {
        build(gcx, gcx.get_type(id), &collector.overrides, &mut done);
    }
    gcx.dcx().ok()
}

/// Inherited entries belong to the subclass, including their generic identity
/// and result type. The base implementation's extension substitution is kept
/// separate so publication, field defaults and cleanup use the subclass layout.
fn inherit_designated<'ctx>(
    gcx: Gcx<'ctx>,
    class: Ty<'ctx>,
    base: Ty<'ctx>,
    inherited: crate::sema::models::ClassInitializer<'ctx>,
) -> Option<crate::sema::models::ClassInitializer<'ctx>> {
    use crate::sema::models::{
        Generics, LabeledFunctionSignature, SyntheticDefinition, SyntheticDefinitionKind,
    };
    use crate::sema::tycheck::utils::instantiate::{
        instantiate_const_with_args, instantiate_signature_with_args,
    };
    let TyKind::Adt(def, class_args) = class.kind() else {
        return None;
    };
    let source = inherited.definition;
    let id = gcx.allocate_synthetic_id(def.id.package());
    let source_generics = gcx.generics_of(source);
    // If the nominal class does not determine the source extension, retain
    // both environments in a private parent scope. Keeping class parameters
    // first preserves unrelated arguments and normal nominal bounds.
    let source_environment = gcx
        .class_method_arguments(base, source, GenericArguments::empty())
        .is_none();
    let (parent, parent_identity) = if source_environment {
        let environment = initializer_environment(gcx, class, source)?;
        (
            Some(environment),
            GenericsBuilder::identity_for_item(gcx, environment),
        )
    } else {
        (Some(def.id), class_args)
    };
    let parent_count = parent_identity.len();
    let mut parameters = source_generics.parameters.clone();
    for (index, parameter) in parameters.iter_mut().enumerate() {
        parameter.id = gcx.allocate_synthetic_id(def.id.package());
        parameter.index = parent_count + index;
    }
    let generics = gcx.store.arenas.generics.alloc(Generics {
        parameters,
        parent,
        parent_count,
        has_self: false,
    });
    let span = gcx.definition_ident(def.id).span;
    let kind = SyntheticDefinitionKind::InheritedClassInitializer {
        class: def.id,
        initializer: source,
    };
    let mut identity = parent_identity.to_vec();
    for (new, old) in generics.parameters.iter().zip(&source_generics.parameters) {
        use crate::sema::models::{Const, ConstKind, GenericArgument};
        let marker = crate::sema::tycheck::utils::generics::generic_parameter_marker(new);
        identity.push(match new.kind {
            GenericParameterDefinitionKind::Type { .. } => {
                GenericArgument::Type(Ty::new(TyKind::Parameter(marker), gcx))
            }
            GenericParameterDefinitionKind::Const { .. } => {
                let prior = gcx.try_generic_const_param_ty(old.id)?;
                // The parameter's type only refers to earlier parameters.
                let own_args = gcx
                    .store
                    .interners
                    .intern_generic_args_slice(&identity[parent_count..]);
                let prior_args = if source_environment {
                    gcx.store
                        .interners
                        .intern_generic_args_slice(&identity[class_args.len()..])
                } else {
                    gcx.class_method_arguments(base, source, own_args)?
                };
                let ty = instantiate_ty_with_args(gcx, prior, prior_args);
                gcx.cache_generic_const_param_ty(new.id, ty);
                GenericArgument::Const(Const {
                    ty,
                    kind: ConstKind::Param(marker),
                })
            }
        });
    }
    let identity = gcx.store.interners.intern_generic_args(identity);
    let own_args = gcx
        .store
        .interners
        .intern_generic_args_slice(&identity[parent_count..]);
    let base_args = if source_environment {
        gcx.store
            .interners
            .intern_generic_args_slice(&identity[class_args.len()..])
    } else {
        gcx.class_method_arguments(base, source, own_args)?
    };
    for (new, old) in generics.parameters.iter().zip(&source_generics.parameters) {
        if let Some(default) = gcx.try_generic_type_default(old.id) {
            gcx.cache_generic_type_default(
                new.id,
                instantiate_ty_with_args(gcx, default, base_args),
            );
        }
        if let Some(default) = gcx.try_generic_const_default(old.id) {
            gcx.cache_generic_const_default(
                new.id,
                instantiate_const_with_args(gcx, default, base_args),
            );
        }
    }
    let mut signature = instantiate_signature_with_args(gcx, gcx.get_signature(source), base_args);
    let source_result = gcx.constructor_value(signature.output);
    signature.output = gcx.constructor_result(signature.output, class);
    // Default providers take no values, but their generic environment must be
    // remapped exactly as the constructor's ordinary arguments are.
    for parameter in &mut signature.inputs {
        if let Some(provider) = parameter.default_provider {
            let default = gcx.allocate_synthetic_id(def.id.package());
            let default_signature =
                gcx.store
                    .arenas
                    .function_signatures
                    .alloc(LabeledFunctionSignature {
                        inputs: vec![],
                        output: parameter.ty,
                        is_variadic: false,
                        abi: None,
                    });
            gcx.register_synthetic_definition(
                default,
                SyntheticDefinition {
                    kind: SyntheticDefinitionKind::InheritedInitializerDefault {
                        initializer: id,
                        provider,
                    },
                    name: gcx.intern_symbol("$inherited_init_default"),
                    generics,
                    signature: default_signature,
                    span,
                },
            );
            gcx.cache_signature(default, default_signature.clone());
            gcx.cache_type(default, Ty::from_labeled_signature(gcx, default_signature));
            parameter.default_provider = Some(default);
        }
    }
    let signature = gcx.store.arenas.function_signatures.alloc(signature);
    gcx.register_synthetic_definition(
        id,
        SyntheticDefinition {
            kind,
            name: gcx.intern_symbol("init"),
            generics,
            signature,
            span,
        },
    );
    gcx.cache_signature(id, signature.clone());
    gcx.cache_type(id, Ty::from_labeled_signature(gcx, signature));
    let inherited_parent: FxHashSet<_> =
        crate::sema::tycheck::constraints::canonical_constraints_of(gcx, def.id)
            .into_iter()
            .map(|constraint| constraint.value)
            .collect();
    let mut constraints: Vec<_> =
        crate::sema::tycheck::constraints::canonical_constraints_of(gcx, source)
            .into_iter()
            .map(|value| {
                crate::span::Spanned::new(
                    instantiate_constraint_with_args(gcx, value.value, base_args),
                    value.span,
                )
            })
            .filter(|constraint| !inherited_parent.contains(&constraint.value))
            .collect();
    // The source's stored payload must have exactly this class's base type.
    // Keep component equalities so parameter normalization also protects the
    // private payload representation and propagates inference through chains.
    if let (TyKind::Adt(source, source_args), TyKind::Adt(expected, expected_args)) =
        (source_result.kind(), base.kind())
        && source.id == expected.id
    {
        for (&source, &expected) in source_args.iter().zip(expected_args.iter()) {
            use crate::sema::models::{Constraint, GenericArgument};
            let equality = match (source, expected) {
                (GenericArgument::Type(source), GenericArgument::Type(expected))
                    if source != expected =>
                {
                    Some(Constraint::TypeEquality(source, expected))
                }
                (GenericArgument::Const(source), GenericArgument::Const(expected))
                    if source != expected =>
                {
                    Some(Constraint::TypeEquality(
                        Ty::new(
                            TyKind::Array {
                                element: gcx.types.bool,
                                len: source,
                            },
                            gcx,
                        ),
                        Ty::new(
                            TyKind::Array {
                                element: gcx.types.bool,
                                len: expected,
                            },
                            gcx,
                        ),
                    ))
                }
                _ => None,
            };
            if let Some(equality) = equality {
                constraints.push(crate::span::Spanned::new(equality, span));
            }
        }
    } else if source_result != base {
        constraints.push(crate::span::Spanned::new(
            crate::sema::models::Constraint::TypeEquality(source_result, base),
            span,
        ));
    }
    gcx.update_constraints(id, constraints);
    Some(crate::sema::models::ClassInitializer {
        definition: id,
        implementation: id,
        family: inherited.family,
        owner: class,
        is_convenience: inherited.is_convenience,
        is_required: inherited.is_required,
        is_inherited: true,
        delegations: &[],
    })
}

/// A non-callable scope keeps nominal class parameters first, followed by a
/// flattened copy of the source constructor's parent environment. Its private
/// parameters are inferred through result/argument constraints, never exposed
/// as additional public init-own generic arguments.
fn initializer_environment<'ctx>(
    gcx: Gcx<'ctx>,
    class: Ty<'ctx>,
    source: hir::DefinitionID,
) -> Option<hir::DefinitionID> {
    use crate::sema::models::{
        Const, ConstKind, GenericArgument, Generics, LabeledFunctionSignature, SyntheticDefinition,
        SyntheticDefinitionKind,
    };
    use crate::sema::tycheck::utils::instantiate::instantiate_const_with_args;
    let TyKind::Adt(def, class_args) = class.kind() else {
        return None;
    };
    fn collect(
        gcx: Gcx<'_>,
        id: hir::DefinitionID,
        output: &mut Vec<crate::sema::models::GenericParameterDefinition>,
    ) {
        let generics = gcx.generics_of(id);
        if let Some(parent) = generics.parent {
            collect(gcx, parent, output);
        }
        output.extend(generics.parameters.iter().cloned());
    }
    let mut original = vec![];
    if let Some(parent) = gcx.generics_of(source).parent {
        collect(gcx, parent, &mut original);
    }
    let mut parameters = original.clone();
    let mut source_identity = vec![];
    for (index, (parameter, old)) in parameters.iter_mut().zip(&original).enumerate() {
        parameter.id = gcx.allocate_synthetic_id(def.id.package());
        parameter.index = class_args.len() + index;
        let marker = crate::sema::tycheck::utils::generics::generic_parameter_marker(parameter);
        source_identity.push(match parameter.kind {
            GenericParameterDefinitionKind::Type { .. } => {
                GenericArgument::Type(Ty::new(TyKind::Parameter(marker), gcx))
            }
            GenericParameterDefinitionKind::Const { .. } => {
                let prior = gcx.try_generic_const_param_ty(old.id)?;
                let args = gcx
                    .store
                    .interners
                    .intern_generic_args_slice(&source_identity);
                let ty = instantiate_ty_with_args(gcx, prior, args);
                gcx.cache_generic_const_param_ty(parameter.id, ty);
                GenericArgument::Const(Const {
                    ty,
                    kind: ConstKind::Param(marker),
                })
            }
        });
    }
    let source_identity = gcx.store.interners.intern_generic_args(source_identity);
    for (parameter, old) in parameters.iter().zip(&original) {
        if let Some(ty) = gcx.try_generic_type_default(old.id) {
            gcx.cache_generic_type_default(
                parameter.id,
                instantiate_ty_with_args(gcx, ty, source_identity),
            );
        }
        if let Some(value) = gcx.try_generic_const_default(old.id) {
            gcx.cache_generic_const_default(
                parameter.id,
                instantiate_const_with_args(gcx, value, source_identity),
            );
        }
    }
    let generics = gcx.store.arenas.generics.alloc(Generics {
        parent: Some(def.id),
        parent_count: class_args.len(),
        parameters,
        has_self: false,
    });
    let signature = gcx
        .store
        .arenas
        .function_signatures
        .alloc(LabeledFunctionSignature {
            inputs: vec![],
            output: gcx.types.void,
            is_variadic: false,
            abi: None,
        });
    let id = gcx.allocate_synthetic_id(def.id.package());
    gcx.register_synthetic_definition(
        id,
        SyntheticDefinition {
            kind: SyntheticDefinitionKind::InitializerEnvironment {
                class: def.id,
                initializer: source,
            },
            name: gcx.intern_symbol("$initializer_environment"),
            generics,
            signature,
            span: gcx.definition_ident(def.id).span,
        },
    );
    Some(id)
}

/// Alpha-rename a base constructor's own parameters to the subclass's. Class
/// parameters are substituted through the actual base type first; the owned
/// result is deliberately excluded because it names the constructed class.
fn same_signature<'ctx>(
    gcx: Gcx<'ctx>,
    class: Ty<'ctx>,
    actual: hir::DefinitionID,
    owner: Ty<'ctx>,
    inherited: hir::DefinitionID,
) -> Option<(GenericArguments<'ctx>, GenericArguments<'ctx>)> {
    let own = gcx.generics_of(actual);
    let base = gcx.generics_of(inherited);
    if own.parameters.len() != base.parameters.len() {
        return None;
    }
    let identity = GenericsBuilder::identity_for_item(gcx, actual);
    let method_args = gcx
        .store
        .interners
        .intern_generic_args_slice(&identity[own.parent_count..]);
    let actual_args = gcx.class_method_arguments(class, actual, method_args)?;
    let base_args = gcx.class_method_arguments(owner, inherited, method_args)?;
    for (own, base) in own.parameters.iter().zip(&base.parameters) {
        match (&own.kind, &base.kind) {
            (
                GenericParameterDefinitionKind::Type { .. },
                GenericParameterDefinitionKind::Type { .. },
            ) => {}
            (
                GenericParameterDefinitionKind::Const { .. },
                GenericParameterDefinitionKind::Const { .. },
            ) => {
                let a = gcx.try_generic_const_param_ty(own.id)?;
                let b = gcx.try_generic_const_param_ty(base.id)?;
                if instantiate_ty_with_args(gcx, a, actual_args)
                    != instantiate_ty_with_args(gcx, b, base_args)
                {
                    return None;
                }
            }
            _ => return None,
        }
    }
    let actual_sig = gcx.get_signature(actual);
    let inherited_sig = gcx.get_signature(inherited);
    if actual_sig.inputs.len() != inherited_sig.inputs.len()
        || actual_sig.abi != inherited_sig.abi
        || actual_sig.is_variadic != inherited_sig.is_variadic
    {
        return None;
    }
    actual_sig
        .inputs
        .iter()
        .zip(&inherited_sig.inputs)
        .all(|(a, b)| {
            a.label == b.label
                && normalize_aliases(gcx, instantiate_ty_with_args(gcx, a.ty, actual_args))
                    == normalize_aliases(gcx, instantiate_ty_with_args(gcx, b.ty, base_args))
        })
        .then_some((actual_args, base_args))
}

#[cfg(test)]
mod tests {
    #[test]
    fn convenience_inheritance_requires_defaults_and_complete_designated_coverage() {
        crate::test_support::analyze_script(
            "class Base { value: int32 }\nextend Base { init(_ value: int32) { self.value = value }; init(flag: bool) { self.value = 2 }; convenience init() { self.init(7) } }\nclass Automatic: Base { extra: int32 = 1 }\nclass Complete: Base { extra: int32 = 1 }\nextend Complete { override init(_ value: int32) { super.init(value) }; override init(flag: bool) { super.init(flag: flag) } }\nclass Partial: Base { extra: int32 = 1 }\nextend Partial { override init(_ value: int32) { super.init(value) } }\nclass NoDefault: Base { extra: int32 }\nextend NoDefault { override init(_ value: int32) { super.init(value); self.extra = 1 }; override init(flag: bool) { super.init(flag: flag); self.extra = 1 } }\nfunc main() {}",
            |package, gcx| {
                for (name, expected) in [
                    ("Automatic", true),
                    ("Complete", true),
                    ("Partial", false),
                    ("NoDefault", false),
                ] {
                    let id = package
                        .root
                        .declarations
                        .iter()
                        .find(|declaration| declaration.identifier.symbol.as_str() == name)
                        .unwrap()
                        .id;
                    assert_eq!(
                        gcx.class_info(gcx.get_type(id))
                            .unwrap()
                            .initializers
                            .iter()
                            .any(|entry| entry.is_convenience),
                        expected,
                        "{name}"
                    );
                }
            },
        );
    }

    #[test]
    fn inaccessible_designated_entries_remain_hidden_but_support_convenience_delegation() {
        crate::test_support::analyze_script(
            "class Base { value: int32 }\nextend Base { private init(_ value: int32) { self.value = value }; convenience init() { self.init(7) } }\nclass Child: Base {}\nfunc main() {}",
            |package, gcx| {
                let base = package.root.declarations[0].id;
                let child = package
                    .root
                    .declarations
                    .iter()
                    .find(|declaration| declaration.identifier.symbol.as_str() == "Child")
                    .unwrap()
                    .id;
                let private = gcx.class_info(gcx.get_type(base)).unwrap().initializers[0];
                let entries = gcx.class_info(gcx.get_type(child)).unwrap().initializers;
                let hidden = entries
                    .iter()
                    .find(|entry| entry.family == private.family)
                    .unwrap();
                assert!(!gcx.is_definition_visible(hidden.definition, child));
                assert!(entries.iter().any(|entry| entry.is_convenience));
            },
        );
    }

    #[test]
    fn inherited_convenience_detects_a_cycle_introduced_by_a_subclass_constructor() {
        let diagnostics = crate::test_support::analyze_script_diagnostics(
            "class Base { value: int32 }\nextend Base { init(_ value: int32) { self.value = value }; convenience init() { self.init(7) } }\nclass Child: Base {}\nextend Child { override convenience init(_ value: int32) { self.init() } }\nfunc main() {}",
        );
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.message.contains("delegation cycle")),
            "{diagnostics:#?}"
        );
    }

    #[test]
    fn shaped_override_matches_in_its_declared_extension_context() {
        crate::test_support::analyze_script(
            "struct Box[T] { value: T }\nclass Base[T] { value: T }\nextend[U] Base[Box[U]] { init(_ value: Box[U]) { self.value = value } }\nclass Child[T, V]: Base[T] { extra: [V; 0] = [] }\nextend[U, V] Child[Box[U], V] { override init(_ value: Box[U]) { super.init(value) } }\nfunc main() { value := Child[Box[int32], bool](Box[int32] { value: 3 }) }",
            |_, _| {},
        );
    }

    #[test]
    fn initializer_visibility_is_package_default_with_explicit_public_export() {
        crate::test_support::analyze_script(
            "public class Record {}\nextend Record { init() {}; public init(_ value: int32) {} }\nfunc main() {}",
            |package, gcx| {
                let class = gcx
                    .class_info(gcx.get_type(package.root.declarations[0].id))
                    .unwrap();
                assert!(matches!(
                    gcx.definition_visibility(class.initializers[0].definition),
                    crate::sema::resolve::models::Visibility::Internal(_)
                ));
                assert_eq!(
                    gcx.definition_visibility(class.initializers[1].definition),
                    crate::sema::resolve::models::Visibility::Public
                );
            },
        );
    }

    #[test]
    fn constructor_families_match_generic_base_arguments_and_renamed_parameters() {
        crate::test_support::analyze_script(
            "class Base[T] { value: T }\nextend[T] Base[T] { init[U](_ value: T, tag: U) { self.value = value } }\nclass Child[T]: Base[[T; 2]] {}\nextend[T] Child[T] { override init[V](_ value: [T; 2], tag: V) { super.init(value, tag: tag) } }\nfunc main() {}",
            |package, gcx| {
                let base = gcx
                    .class_info(gcx.get_type(package.root.declarations[0].id))
                    .unwrap();
                let child = gcx
                    .class_info(gcx.get_type(package.root.declarations[2].id))
                    .unwrap();
                assert_eq!(child.initializers[0].family, base.initializers[0].family);
                assert_ne!(
                    child.initializers[0].implementation,
                    base.initializers[0].implementation
                );
                assert!(!child.initializers[0].is_inherited);
            },
        );
    }

    #[test]
    fn base_initialization_deduces_reordered_extension_parameters_from_its_result() {
        crate::test_support::analyze_script(
            "class Base[X, Y] { first: X; second: Y }\nextend[B, A] Base[A, B] { init(_ first: A, _ second: B) { self.first = first; self.second = second } }\nclass Child[X, Y]: Base[Y, X] {}\nextend[B, A] Child[A, B] { override init(_ first: B, _ second: A) { super.init(first, second) } }\nfunc main() {}",
            |_, _| {},
        );
    }

    #[test]
    fn type_name_construction_infers_reordered_extension_arguments_from_result() {
        crate::test_support::analyze_script(
            "class Pair[X, Y] { first: X; second: Y }\nextend[B, A] Pair[A, B] { init(_ first: A, _ second: B) { self.first = first; self.second = second } }\nfunc main() { var pair: Pair[int32, bool] = Pair[int32, bool](7, true) }",
            |_, _| {},
        );
        let diagnostics = crate::test_support::analyze_script_diagnostics(
            "class Pair[X, Y] { first: X; second: Y }\nextend[B, A] Pair[A, B] { init(_ first: A, _ second: B) { self.first = first; self.second = second } }\nfunc main() { pair := Pair[int32, bool](true, 7) }",
        );
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.message.contains("expected bool")),
            "{diagnostics:#?}"
        );
    }

    #[test]
    fn inherited_designated_entries_construct_the_subclass_and_keep_families() {
        crate::test_support::analyze_script(
            "class Base[X, Y] { first: X; second: Y }\nextend[B, A] Base[A, B] { init[U](_ first: A, _ second: B, tag: U) { self.first = first; self.second = second } }\nclass Child[T]: Base[bool, [T; 2]] { count: int32 = 3 }\nclass Grandchild[T]: Child[T] {}\nfunc main() { var child: Child[int32] = Child[int32](true, [1, 2], tag: false); var grandchild: Grandchild[int32] = Grandchild[int32](false, [3, 4], tag: 7) }",
            |package, gcx| {
                let base = gcx
                    .class_info(gcx.get_type(package.root.declarations[0].id))
                    .unwrap();
                for index in [2, 3] {
                    let id = package.root.declarations[index].id;
                    let class = gcx.class_info(gcx.get_type(id)).unwrap();
                    assert_eq!(class.initializers.len(), 1);
                    let entry = class.initializers[0];
                    assert!(entry.is_inherited);
                    assert_eq!(entry.family, base.initializers[0].family);
                    assert_eq!(gcx.get_signature(entry.definition).output, gcx.get_type(id));
                    let identity = super::GenericsBuilder::identity_for_item(gcx, entry.definition);
                    assert!(
                        gcx.inherited_initializer_target(entry.definition, identity)
                            .is_some()
                    );
                }
            },
        );
    }

    #[test]
    fn inherited_context_preserves_unrelated_parameters_and_own_generic_arguments() {
        crate::test_support::analyze_script(
            "struct Box[T] { value: T }\nclass Base[T] { value: T }\nextend[U] Base[Box[U]] { init[Tag, const N: usize](_ value: Box[U], tag: [Tag; N]) { self.value = value } }\nfinal class Child[T, V]: Base[T] { extra: [V; 0] = [] }\nfunc main() { var first: Child[Box[int32], bool] = Child[Box[int32], bool](Box[int32] { value: 7 }, tag: [true, false]); var second: Child[Box[int32], bool] = Child[Box[int32], bool]::init[bool, 2](Box[int32] { value: 9 }, tag: [false, true]) }",
            |_, _| {},
        );
    }

    #[test]
    fn inherited_context_keeps_class_and_initializer_const_parameters_separate() {
        crate::test_support::analyze_script(
            "struct Box[T] { value: T }\nclass Base[T] { value: T }\nextend[U] Base[Box[U]] { init[Tag, const M: usize](_ value: Box[U], tag: [Tag; M]) { self.value = value } }\nfinal class Child[T, const N: usize]: Base[T] { extra: usize = N }\nfunc main() { var child: Child[Box[int32], 3] = Child[Box[int32], 3](Box[int32] { value: 7 }, tag: [true, false]) }",
            |_, _| {},
        );
    }

    #[test]
    fn shaped_initializer_extensions_can_also_declare_borrowing_methods() {
        crate::test_support::analyze_script(
            "struct Box[T] { value: T }\nclass Base[T] { value: T }\nextend[U] Base[Box[U]] { init(_ value: Box[U]) { self.value = value }; func get() -> &Box[U] { &self.value }; }\nfinal class Child[T]: Base[T] {}\nfunc main() { var child: Child[Box[int32]] = Child[Box[int32]](Box[int32] { value: 7 }); var value: &Box[int32] = child.get() }",
            |_, _| {},
        );
    }

    #[test]
    fn shaped_base_initializers_infer_the_subclass_result_in_the_source_environment() {
        crate::test_support::analyze_script(
            "interface Marker {}\nstruct Box[U] { value: U }\nconform[U] Box[U] to Marker {}\nclass Base[T] { value: T }\nextend[U] Base[Box[U]] { init[Tag, const N: usize](_ value: Box[U], tag: [Tag; N]) { self.value = value } }\nclass Child[T: Marker]: Base[T] { count: int32 = 3 }\nfinal class Grandchild[T: Marker]: Child[T] {}\nfunc forward[T](_ value: Box[T]) -> Grandchild[Box[T]] { Grandchild[Box[T]](value, tag: [true, false]) }\nfunc main() { result := forward(Box[int32] { value: 7 }) }",
            |package, gcx| {
                for index in [5, 6] {
                    let class = gcx
                        .class_info(gcx.get_type(package.root.declarations[index].id))
                        .unwrap();
                    assert_eq!(class.initializers.len(), 1);
                    let parent = gcx
                        .generics_of(class.initializers[0].definition)
                        .parent
                        .unwrap();
                    assert!(matches!(
                        gcx.store.synthetic_definitions.borrow()[&parent].kind,
                        crate::sema::models::SyntheticDefinitionKind::InitializerEnvironment { .. }
                    ));
                }
            },
        );
    }

    #[test]
    fn specialized_base_initializer_cannot_construct_an_incompatible_subclass() {
        crate::test_support::analyze_script(
            "class Base[T] { value: T }\nextend Base[int32] { init() { self.value = 7 } }\nclass Child[T]: Base[T] {}\nfunc main() { var child: Child[int32] = Child[int32]() }",
            |_, _| {},
        );
        let diagnostics = crate::test_support::analyze_script_diagnostics(
            "class Base[T] { value: T }\nextend Base[int32] { init() { self.value = 7 } }\nclass Child[T]: Base[T] {}\nfunc main() { var child: Child[bool] = Child[bool]() }",
        );
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.message.contains("bool")),
            "{diagnostics:#?}"
        );
    }

    #[test]
    fn inherited_designated_entries_keep_const_parameters_and_bounds() {
        crate::test_support::analyze_script(
            "class Base[X, Y] {}\nextend[B, A] Base[A, B] { init[const N: usize](_ values: [A; N], _ flag: B) {} }\nclass Child[T]: Base[T, bool] {}\nfunc main() { var child: Child[int32] = Child[int32]([1, 2], true) }",
            |_, _| {},
        );
        let diagnostics = crate::test_support::analyze_script_diagnostics(
            "interface Marked {}\nclass Base {}\nextend Base { init[T: Marked](_ value: T) {} }\nclass Child: Base {}\nfunc main() { child := Child(1) }",
        );
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.message.contains("Marked")),
            "{diagnostics:#?}"
        );
    }

    #[test]
    fn inherited_designated_entries_require_defaults_and_no_designated_declaration() {
        for source in [
            "class Base {}\nextend Base { init(_ value: int32) {} }\nclass Child: Base { missing: int32 }\nfunc main() { value := Child(1) }",
            "class Base {}\nextend Base { init(_ value: int32) {} }\nclass Child: Base {}\nextend Child { init(other: bool) { super.init(1) } }\nfunc main() { value := Child(1) }",
            "class Base {}\nextend Base { private init(_ value: int32) {} }\nclass Child: Base {}\nfunc main() { value := Child(1) }",
        ] {
            let diagnostics = crate::test_support::analyze_script_diagnostics(source);
            assert!(!diagnostics.is_empty(), "{source}");
            assert!(
                !diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.message.contains("requires override init")),
                "{diagnostics:#?}"
            );
        }
    }

    #[test]
    fn constructor_override_spelling_requires_a_matching_designated_signature() {
        for (source, expected) in [
            (
                "class Base {}\nextend Base { init(_ value: int32) {} }\nclass Child: Base {}\nextend Child { init(_ value: int32) { super.init(value) } }\nfunc main() {}",
                "requires override init",
            ),
            (
                "class Base {}\nextend Base { init(value: int32) {} }\nclass Child: Base {}\nextend Child { override init(other: int32) { super.init(value: other) } }\nfunc main() {}",
                "no matching base designated",
            ),
            (
                "class Root {}\nextend Root { override init() {} }\nfunc main() {}",
                "no matching base designated",
            ),
            (
                "struct Value {}\nextend Value { override init() {} }\nfunc main() {}",
                "requires a class designated",
            ),
        ] {
            let diagnostics = crate::test_support::analyze_script_diagnostics(source);
            assert!(
                diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.message.contains(expected)),
                "{source}\n{diagnostics:#?}"
            );
        }
    }

    #[test]
    fn constructor_override_cannot_narrow_generic_or_extension_conditions() {
        for (source, expected) in [
            (
                "interface Available {}\nclass Base {}\nextend Base { init[T](_ value: T) {} }\nclass Child: Base {}\nextend Child { override init[U: Available](_ value: U) { super.init(value) } }\nfunc main() {}",
                "generic constraints must match",
            ),
            (
                "interface Available {}\nclass Base[T] {}\nextend[T] Base[T] { init(_ value: T) {} }\nclass Child[T]: Base[T] {}\nextend[T: Available] Child[T] { override init(_ value: T) { super.init(value) } }\nfunc main() {}",
                "stronger conditions",
            ),
            (
                "public class Base {}\nextend Base { public init(_ value: int32) {} }\npublic class Child: Base {}\nextend Child { override init(_ value: int32) { super.init(value) } }\nfunc main() {}",
                "must remain public",
            ),
        ] {
            let diagnostics = crate::test_support::analyze_script_diagnostics(source);
            assert!(
                diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.message.contains(expected)),
                "{source}\n{diagnostics:#?}"
            );
        }
    }
}
