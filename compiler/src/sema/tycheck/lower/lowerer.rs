use crate::{
    compile::context::GlobalContext,
    hir::{self, DefinitionID, DefinitionKind, Resolution},
    sema::{
        models::{
            AdtDef, AdtKind, AliasKind, AssociatedTypeBinding, Const, ConstKind, ConstValue,
            Constraint, GenericArgument, GenericArguments, GenericParameter,
            GenericParameterDefinition, GenericParameterDefinitionKind, InterfaceDefinition,
            InterfaceReference, Ty, TyKind,
        },
        resolve::models::{PrimaryType, TypeHead},
        tycheck::{
            lower::LoweringRequest,
            utils::{
                const_eval::eval_const_expression,
                instantiate::{instantiate_interface_ref_with_args, instantiate_ty_with_args},
                type_head_from_value_ty,
            },
        },
    },
    span::{Span, Symbol},
};

use rustc_hash::FxHashSet;
use std::collections::VecDeque;

thread_local! {
    static LOWERING_REQUEST: LoweringRequest = LoweringRequest::new();
}

pub trait TypeLowerer<'ctx> {
    fn gcx(&self) -> GlobalContext<'ctx>;
    fn current_definition(&self) -> Option<hir::DefinitionID> {
        None
    }
    fn lowerer(&self) -> &dyn TypeLowerer<'ctx>
    where
        Self: Sized,
    {
        self
    }
    fn ty_infer(&self, param: Option<&GenericParameterDefinition>, span: Span) -> Ty<'ctx>;
}

impl<'ctx> dyn TypeLowerer<'ctx> + '_ {
    pub fn lower_type(&self, node: &hir::Type) -> Ty<'ctx> {
        let gcx = self.gcx();
        match &node.kind {
            hir::TypeKind::Nominal(path) => self.lower_nominal_type(node.id, path),
            hir::TypeKind::Pointer(node, mutability) => {
                let internal = self.lower_type(node);
                Ty::new(TyKind::Pointer(internal, *mutability), gcx)
            }
            hir::TypeKind::Reference(node, mutability) => {
                let internal = self.lower_type(node);
                Ty::new(TyKind::Reference(internal, *mutability), gcx)
            }
            hir::TypeKind::Tuple(elements) => {
                let mut lowered = Vec::with_capacity(elements.len());
                for elem in elements {
                    lowered.push(self.lower_type(elem));
                }
                Ty::new(
                    TyKind::Tuple(gcx.store.interners.intern_ty_list(lowered)),
                    gcx,
                )
            }
            hir::TypeKind::Array { size, element } => {
                let element = self.lower_type(element);
                let len = self.lower_array_length(size);
                Ty::new(TyKind::Array { element, len }, gcx)
            }
            hir::TypeKind::Function { inputs, output } => {
                let mut lowered_inputs = Vec::with_capacity(inputs.len());
                for input in inputs {
                    lowered_inputs.push(self.lower_type(input));
                }
                let lowered_inputs = gcx.store.interners.intern_ty_list(lowered_inputs);
                let output = self.lower_type(output);
                Ty::new(
                    TyKind::FnPointer {
                        inputs: lowered_inputs,
                        output,
                    },
                    gcx,
                )
            }
            hir::TypeKind::BoxedExistential { interfaces } => {
                let self_ty = gcx.types.self_type_parameter;
                let mut lowered = Vec::with_capacity(interfaces.len());
                for interface in interfaces {
                    lowered.push(self.lower_interface_reference(self_ty, interface));
                }
                let list = gcx.store.arenas.global.alloc_slice_copy(&lowered);
                Ty::new(TyKind::BoxedExistential { interfaces: list }, gcx)
            }
            hir::TypeKind::QualifiedAccess {
                target,
                interface,
                member,
            } => self.lower_qualified_access(node, target, interface, member),
            hir::TypeKind::Never => Ty::new(TyKind::Never, gcx),
            hir::TypeKind::Infer => unreachable!(),
        }
    }

    fn lower_nominal_type(&self, node_id: hir::NodeID, path: &hir::ResolvedPath) -> Ty<'ctx> {
        match path {
            hir::ResolvedPath::Resolved(path) => self.lower_resolved_type_path(node_id, path),
            hir::ResolvedPath::Relative(base_ty, segment) => {
                self.lower_relative_type_path(base_ty, segment)
            }
        }
    }

    fn lower_resolved_type_path(&self, _: hir::NodeID, path: &hir::Path) -> Ty<'ctx> {
        let resolution = path.resolution.clone();
        let gcx = self.gcx();
        let segment = path.segments.last().expect("path must have segments");
        match resolution {
            Resolution::PrimaryType(k) => {
                let message = format!(
                    "'{}' does not accept generic arguments",
                    segment.identifier.symbol.as_str()
                );
                let _ = check_no_type_arguments(segment, gcx, message);
                match k {
                    PrimaryType::Int(k) => Ty::new_int(gcx, k),
                    PrimaryType::UInt(k) => Ty::new_uint(gcx, k),
                    PrimaryType::Float(k) => Ty::new_float(gcx, k),
                    PrimaryType::String => gcx.types.string,
                    PrimaryType::Bool => gcx.types.bool,
                    PrimaryType::Rune => gcx.types.rune,
                }
            }
            Resolution::Foundation(decl) => match self.lower_foundation_type(path, decl) {
                Some(ty) => ty,
                None => gcx.types.error,
            },
            Resolution::Definition(id, DefinitionKind::TypeParameter) => {
                let message = format!(
                    "'{}' does not accept generic arguments",
                    segment.identifier.symbol.as_str()
                );
                let _ = check_no_type_arguments(segment, gcx, message);
                gcx.get_type(id)
            }
            Resolution::Definition(id, kind) => {
                if let Some(from) = self.current_definition() {
                    if !gcx.is_definition_visible(id, from) {
                        let name = gcx.definition_ident(id).symbol;
                        gcx.dcx().emit_error(
                            format!("type '{}' is not visible here", name).into(),
                            Some(path.span),
                        );
                        return gcx.types.error;
                    }
                }
                let _ = check_generics_prohibited(id, segment, gcx);
                let args = self.lower_type_arguments(id, segment);
                match kind {
                    crate::sema::resolve::models::DefinitionKind::Struct
                    | crate::sema::resolve::models::DefinitionKind::Enum => {
                        let ident = gcx.definition_ident(id);
                        let def = AdtDef {
                            name: ident.symbol,
                            kind: match kind {
                                crate::sema::resolve::models::DefinitionKind::Enum => AdtKind::Enum,
                                _ => AdtKind::Struct,
                            },
                            id,
                        };
                        // Return the Adt directly - args are already lowered and in place.
                        // Do NOT call instantiate_ty_with_args here, as that would
                        // incorrectly substitute type parameters within the args themselves.
                        Ty::new(TyKind::Adt(def, args), gcx)
                    }
                    crate::sema::resolve::models::DefinitionKind::TypeAlias => {
                        // Resolve alias in place with cycle detection
                        let ty = self.resolve_alias(id);
                        instantiate_ty_with_args(gcx, ty, args)
                    }
                    _ => todo!("nominal type lowering for {kind:?}"),
                }
            }
            Resolution::SelfTypeAlias(id) => {
                let message = "cannot apply generic arguments to `Self`".to_string();
                let _ = check_no_type_arguments(segment, gcx, message);
                match gcx.definition_kind(id) {
                    crate::sema::resolve::models::DefinitionKind::Struct
                    | crate::sema::resolve::models::DefinitionKind::Enum => gcx.get_type(id),
                    crate::sema::resolve::models::DefinitionKind::Impl => {
                        if let Some(self_ty) = gcx.get_impl_self_ty(id) {
                            self_ty
                        } else {
                            let Some(head) = gcx.get_impl_type_head(id) else {
                                return gcx.types.error;
                            };
                            match head {
                                _ => todo!("Self type alias lowering for {head:?}"),
                            }
                        }
                    }
                    other => todo!("Self type alias lowering for {other:?}"),
                }
            }
            Resolution::InterfaceSelfTypeParameter(_interface_id) => {
                // Inside an interface, `Self` refers to the abstract Self type parameter
                let message = "cannot apply generic arguments to `Self`".to_string();
                let _ = check_no_type_arguments(segment, gcx, message);
                gcx.types.self_type_parameter
            }
            Resolution::Error => gcx.types.error,
            Resolution::SelfConstructor(..)
            | Resolution::FunctionSet(..)
            | Resolution::LocalVariable(_) => {
                unreachable!("value resolution")
            }
        }
    }

    pub fn lower_type_arguments(
        &self,
        def_id: DefinitionID,
        segment: &hir::PathSegment,
    ) -> GenericArguments<'ctx> {
        let (args, bindings) = self.lower_generic_args(def_id, segment, None);
        if !bindings.is_empty() {
            self.gcx().dcx().emit_error(
                "associated type bindings are not allowed here".into(),
                Some(segment.span),
            );
        }
        args
    }

    fn lower_generic_args(
        &self,
        id: DefinitionID,
        segment: &hir::PathSegment,
        self_ty: Option<Ty<'ctx>>,
    ) -> (GenericArguments<'ctx>, &'ctx [AssociatedTypeBinding<'ctx>]) {
        let gcx = self.gcx();
        let _ = check_generic_arg_count(id, segment, gcx);

        let generics = gcx.generics_of(id);

        let mut output = vec![];
        let mut bindings = vec![];

        let arguments = segment
            .arguments
            .clone()
            .map(|v| v.arguments)
            .unwrap_or_default();
        let span = segment
            .arguments
            .as_ref()
            .map(|f| f.span)
            .unwrap_or(segment.span);
        let mut args_iter = arguments.iter().peekable();
        let mut params_iter = generics.parameters.iter().peekable();

        loop {
            // Check for associated type bindings first
            if let Some(hir::TypeArgument::AssociatedType(ident, ty)) = args_iter.peek() {
                let lowered_ty = self.lower_type(ty);
                bindings.push(AssociatedTypeBinding {
                    name: ident.symbol,
                    ty: lowered_ty,
                });
                args_iter.next();
                continue;
            }

            match (args_iter.peek(), params_iter.peek()) {
                (_, Some(&param)) if generics.has_self && param.index == 0 => {
                    // Self must always be provided for interface references
                    let ty =
                        self_ty.expect("ICE: Self type must be provided for interface references");
                    output.push(GenericArgument::Type(ty));
                    params_iter.next();
                }
                (Some(&arg), Some(&param)) => {
                    let lowered = match (&param.kind, arg) {
                        (
                            GenericParameterDefinitionKind::Type { .. },
                            hir::TypeArgument::Type(ty),
                        ) => GenericArgument::Type(self.lower_type(ty)),
                        (
                            GenericParameterDefinitionKind::Const { ty, .. },
                            hir::TypeArgument::Const(c),
                        ) => {
                            let expected_ty = self.lower_type(ty);
                            GenericArgument::Const(self.lower_const_argument(expected_ty, c))
                        }
                        (
                            GenericParameterDefinitionKind::Type { .. },
                            hir::TypeArgument::Const(c),
                        ) => {
                            gcx.dcx()
                                .emit_error("expected type argument".into(), Some(c.value.span));
                            GenericArgument::Type(gcx.types.error)
                        }
                        (
                            GenericParameterDefinitionKind::Const { ty: param_ty, .. },
                            hir::TypeArgument::Type(ty_arg),
                        ) => {
                            let expected_ty = self.lower_type(param_ty);
                            if let Some(param) = self.const_param_from_type_arg(ty_arg) {
                                if param.ty != expected_ty
                                    && param.ty != gcx.types.error
                                    && expected_ty != gcx.types.error
                                {
                                    let message = format!(
                                        "const argument does not match parameter type '{}'",
                                        expected_ty.format(gcx)
                                    );
                                    gcx.dcx().emit_error(message, Some(ty_arg.span));
                                    GenericArgument::Const(self.error_const())
                                } else {
                                    GenericArgument::Const(Const {
                                        ty: expected_ty,
                                        kind: param.kind,
                                    })
                                }
                            } else {
                                gcx.dcx().emit_error(
                                    "expected const argument".into(),
                                    Some(ty_arg.span),
                                );
                                GenericArgument::Const(self.error_const())
                            }
                        }
                        (_, hir::TypeArgument::AssociatedType(..)) => {
                            unreachable!("Associated types handled above")
                        }
                    };
                    output.push(lowered);
                    args_iter.next();
                    params_iter.next();
                }
                (Some(_), None) => {
                    break;
                }
                (None, Some(&param)) => {
                    match &param.kind {
                        // ---- provided default ----
                        GenericParameterDefinitionKind::Type { default: Some(d) } => {
                            let ty = self.lower_type(&d);
                            output.push(GenericArgument::Type(ty));
                        }

                        // ---- no default ----
                        GenericParameterDefinitionKind::Type { default: None } => {
                            let ty = self.ty_infer(Some(param), span);
                            output.push(GenericArgument::Type(ty));
                        }

                        GenericParameterDefinitionKind::Const { ty, default } => {
                            let expected_ty = self.lower_type(ty);
                            if let Some(default) = default {
                                let konst = self.lower_const_argument(expected_ty, default);
                                output.push(GenericArgument::Const(konst));
                            } else {
                                gcx.dcx()
                                    .emit_error("missing const argument".into(), Some(span));
                                output.push(GenericArgument::Const(self.error_const()));
                            }
                        }
                    }
                    params_iter.next();
                }
                (None, None) => break,
            }
        }

        (
            gcx.store.interners.intern_generic_args(output),
            gcx.store.arenas.global.alloc_slice_copy(&bindings),
        )
    }

    pub fn lower_const_argument(
        &self,
        expected_ty: Ty<'ctx>,
        anon: &hir::AnonConst,
    ) -> Const<'ctx> {
        let gcx = self.gcx();
        if let Some(param) = self.lower_const_parameter(anon) {
            if param.ty != expected_ty
                && param.ty != gcx.types.error
                && expected_ty != gcx.types.error
            {
                let message = format!(
                    "const argument does not match parameter type '{}'",
                    expected_ty.format(gcx)
                );
                gcx.dcx().emit_error(message, Some(anon.value.span));
                return self.error_const();
            }
            return Const {
                ty: expected_ty,
                kind: param.kind,
            };
        }
        let Some(value) = eval_const_expression(gcx, &anon.value) else {
            return self.error_const();
        };

        if !const_value_matches_type(value, expected_ty) {
            let message = format!(
                "const argument does not match parameter type '{}'",
                expected_ty.format(gcx)
            );
            gcx.dcx().emit_error(message, Some(anon.value.span));
            return self.error_const();
        }

        Const {
            ty: expected_ty,
            kind: ConstKind::Value(value),
        }
    }

    pub fn error_const(&self) -> Const<'ctx> {
        let gcx = self.gcx();
        Const {
            ty: gcx.types.error,
            kind: ConstKind::Value(ConstValue::Unit),
        }
    }

    pub fn lower_interface_reference(
        &self,
        self_ty: Ty<'ctx>,
        node: &hir::PathNode,
    ) -> InterfaceReference<'ctx> {
        let path = match &node.path {
            hir::ResolvedPath::Resolved(path) => path,
            _ => {
                unreachable!("ICE: Interface Paths must be fully resolved")
            }
        };

        let interface_id = match &path.resolution {
            Resolution::Definition(id, DefinitionKind::Interface) => *id,
            _ => unreachable!("ICE: not an interface"),
        };

        let segment = path.segments.last().unwrap();
        let (arguments, bindings) = self.lower_generic_args(interface_id, segment, Some(self_ty));

        InterfaceReference {
            id: interface_id,
            arguments,
            bindings,
        }
    }

    /// Lower T.Element style associated type access
    fn lower_relative_type_path(
        &self,
        base_ty: &hir::Type,
        segment: &hir::PathSegment,
    ) -> Ty<'ctx> {
        let gcx = self.gcx();
        let base_ty = self.lower_type(base_ty);
        if let TyKind::Parameter(param) = base_ty.kind() {
            return self.lower_projection_type_path(param, segment);
        }
        let Some(head) = type_head_from_value_ty(base_ty) else {
            gcx.dcx().emit_error(
                "cannot resolve associated types on this type".into(),
                Some(segment.span),
            );
            return gcx.types.error;
        };

        let name = segment.identifier.symbol;
        let mut candidates: Vec<(DefinitionID, Span)> = Vec::new();

        // For reference/pointer types, we need to filter by the actual inner type
        // since TypeHead::Reference only contains mutability, not the inner type
        let needs_self_ty_match = matches!(head, TypeHead::Reference(_));

        // Temporary storage for candidates (Alias ID, Span, Extension ID)
        let mut raw_candidates: Vec<(DefinitionID, Span, Option<DefinitionID>)> = Vec::new();

        let mut collect = |db: &mut crate::compile::context::TypeDatabase<'ctx>| {
            if let Some(bucket) = db.alias_table.by_type.get(&head) {
                if let Some(entry) = bucket.aliases.get(&name) {
                    let alias_id = entry.0;
                    let span = entry.1;
                    let mut extension_id = None;

                    if let Some(alias_def) = db.alias_table.aliases.get(&alias_id) {
                        extension_id = alias_def.extension_id;
                    }

                    raw_candidates.push((alias_id, span, extension_id));
                }
            }
        };

        gcx.with_session_type_database(|db| collect(db));

        for index in gcx.visible_packages() {
            gcx.with_type_database(index, |db| collect(db));
        }

        for (alias_id, span, ext_id) in raw_candidates {
            // For reference/pointer types, verify the extension's self type matches
            if needs_self_ty_match {
                if let Some(ext_id) = ext_id {
                    if let Some(ext_self_ty) = gcx.get_impl_self_ty(ext_id) {
                        // Only include if the impl's self type matches our base_ty
                        if self.types_match_for_assoc_lookup(base_ty, ext_self_ty) {
                            candidates.push((alias_id, span));
                        }
                        continue;
                    }
                }
                // If we can't verify, include the candidate (fallback)
                candidates.push((alias_id, span));
            } else {
                candidates.push((alias_id, span));
            }
        }

        if candidates.is_empty() {
            gcx.dcx().emit_error(
                format!(
                    "unknown associated type '{}' on type '{}'",
                    name.as_str(),
                    base_ty.format(gcx)
                ),
                Some(segment.span),
            );
            return gcx.types.error;
        }

        let visible: Vec<_> = if let Some(from) = self.current_definition() {
            candidates
                .into_iter()
                .filter(|(id, _)| gcx.is_definition_visible(*id, from))
                .collect()
        } else {
            candidates
        };

        // Deduplicate by definition ID - the same alias may appear in both
        // session database and package databases
        let mut seen_ids = FxHashSet::default();
        let visible: Vec<_> = visible
            .into_iter()
            .filter(|(id, _)| seen_ids.insert(*id))
            .collect();

        if visible.is_empty() {
            gcx.dcx().emit_error(
                format!("associated type '{}' is not visible here", name.as_str()),
                Some(segment.span),
            );
            return gcx.types.error;
        }

        if visible.len() > 1 {
            gcx.dcx().emit_error(
                format!(
                    "ambiguous associated type '{}' on type '{}'",
                    name.as_str(),
                    base_ty.format(gcx)
                ),
                Some(segment.span),
            );
            return gcx.types.error;
        }

        let (alias_id, _) = visible[0];
        let _ = check_generics_prohibited(alias_id, segment, gcx);
        let args = self.lower_type_arguments(alias_id, segment);
        let ty = self.resolve_alias(alias_id);
        instantiate_ty_with_args(gcx, ty, args)
    }

    /// Check if two types match for associated type lookup purposes.
    /// This is used to filter candidates when looking up associated types on reference/pointer types.
    /// We compare the inner nominal types to ensure we match the correct extension.
    fn types_match_for_assoc_lookup(&self, base_ty: Ty<'ctx>, ext_self_ty: Ty<'ctx>) -> bool {
        match (base_ty.kind(), ext_self_ty.kind()) {
            // Reference types: compare inner types
            (TyKind::Reference(inner1, m1), TyKind::Reference(inner2, m2)) if m1 == m2 => {
                self.types_match_for_assoc_lookup(inner1, inner2)
            }
            // Pointer types: compare inner types
            (TyKind::Pointer(inner1, m1), TyKind::Pointer(inner2, m2)) if m1 == m2 => {
                self.types_match_for_assoc_lookup(inner1, inner2)
            }
            // Nominal types: compare by definition ID (ignoring generic args which may have params)
            (TyKind::Adt(def1, _), TyKind::Adt(def2, _)) => def1.id == def2.id,
            // Primitives and other types: just check equality
            _ => base_ty == ext_self_ty,
        }
    }

    /// Lower qualified type access: `(T as I).Member`
    /// This explicitly specifies which interface's associated type to use.
    fn lower_qualified_access(
        &self,
        node: &hir::Type,
        target: &hir::Type,
        interface: &hir::Type,
        member: &crate::span::Identifier,
    ) -> Ty<'ctx> {
        let gcx = self.gcx();

        // 1. Lower the target type T
        let target_ty = self.lower_type(target);
        if target_ty.is_error() {
            return gcx.types.error;
        }

        // 2. Extract interface ID from the interface type
        let hir::TypeKind::Nominal(ref resolved_path) = interface.kind else {
            gcx.dcx().emit_error(
                "interface in qualified access must be a nominal type".into(),
                Some(interface.span),
            );
            return gcx.types.error;
        };

        let hir::ResolvedPath::Resolved(path) = resolved_path else {
            gcx.dcx().emit_error(
                "interface in qualified access must be resolved".into(),
                Some(interface.span),
            );
            return gcx.types.error;
        };

        let interface_id = match &path.resolution {
            Resolution::Definition(id, DefinitionKind::Interface) => *id,
            _ => {
                gcx.dcx().emit_error(
                    "qualified access requires an interface type".into(),
                    Some(interface.span),
                );
                return gcx.types.error;
            }
        };

        // 3. Get type head for target type
        let Some(type_head) = type_head_from_value_ty(target_ty) else {
            gcx.dcx().emit_error(
                format!(
                    "cannot use qualified access on type '{}'",
                    target_ty.format(gcx)
                ),
                Some(target.span),
            );
            return gcx.types.error;
        };

        // 4. Build interface reference with proper arguments
        let segment = path.segments.last().expect("path must have segments");
        let (interface_args, bindings) =
            self.lower_generic_args(interface_id, segment, Some(target_ty));
        let interface_ref = InterfaceReference {
            id: interface_id,
            arguments: interface_args,
            bindings,
        };

        // 5. Look up associated type in interface requirements
        let interface_name = gcx.definition_ident(interface_id).symbol;
        let Some(requirements) = gcx.get_interface_requirements(interface_id) else {
            gcx.dcx().emit_error(
                format!(
                    "interface '{}' has no requirements",
                    interface_name.as_str()
                ),
                Some(interface.span),
            );
            return gcx.types.error;
        };

        let assoc_type = requirements.types.iter().find(|t| t.name == member.symbol);

        let Some(assoc_type) = assoc_type else {
            gcx.dcx().emit_error(
                format!(
                    "no associated type '{}' in interface '{}'",
                    member.symbol.as_str(),
                    interface_name.as_str()
                ),
                Some(member.span),
            );
            return gcx.types.error;
        };

        // 6. Resolve conformance witness
        let witness =
            crate::sema::tycheck::resolve_conformance_witness(gcx, type_head, interface_ref);

        let Some(witness) = witness else {
            gcx.dcx().emit_error(
                format!(
                    "type '{}' does not conform to interface '{}'",
                    target_ty.format(gcx),
                    interface_name.as_str()
                ),
                Some(node.span),
            );
            return gcx.types.error;
        };

        // 7. Look up the associated type in the witness
        let Some(witness_ty) = witness.type_witnesses.get(&assoc_type.id) else {
            gcx.dcx().emit_error(
                format!(
                    "associated type '{}' not satisfied in conformance",
                    member.symbol.as_str()
                ),
                Some(member.span),
            );
            return gcx.types.error;
        };

        *witness_ty
    }

    fn lower_projection_type_path(
        &self,
        base_param: GenericParameter,
        segment: &hir::PathSegment,
    ) -> Ty<'ctx> {
        let gcx = self.gcx();
        let name = segment.identifier.symbol;

        let Some(def_id) = self.current_definition() else {
            gcx.dcx().emit_error(
                format!(
                    "cannot resolve associated type '{}' without a surrounding definition",
                    name.as_str()
                ),
                Some(segment.span),
            );
            return gcx.types.error;
        };

        let constraints = self.constraints_in_scope(def_id);
        let mut candidates: Vec<(DefinitionID, InterfaceReference<'ctx>)> = Vec::new();
        let mut has_bounds = false;

        for constraint in constraints {
            let Constraint::Bound { ty, interface } = constraint.value else {
                continue;
            };
            if matches!(ty.kind(), TyKind::Parameter(param) if param == base_param) {
                has_bounds = true;
                self.collect_projection_candidates(interface, name, &mut candidates);
            }
        }

        if candidates.is_empty() {
            let message = if has_bounds {
                format!(
                    "no associated type '{}' found in bounds for '{}'",
                    name.as_str(),
                    base_param.name.as_str()
                )
            } else {
                format!(
                    "cannot resolve associated type '{}' on '{}' without interface bounds",
                    name.as_str(),
                    base_param.name.as_str()
                )
            };
            gcx.dcx().emit_error(message, Some(segment.span));
            return gcx.types.error;
        }

        let mut seen = FxHashSet::default();
        candidates.retain(|candidate| seen.insert(*candidate));

        if candidates.len() > 1 {
            let mut names: Vec<_> = candidates
                .iter()
                .map(|(_, iface)| iface.format(gcx))
                .collect();
            names.sort();
            names.dedup();
            gcx.dcx().emit_error(
                format!(
                    "ambiguous associated type '{}' for '{}'; candidates: {}",
                    name.as_str(),
                    base_param.name.as_str(),
                    names.join(", "),
                ),
                Some(segment.span),
            );
            return gcx.types.error;
        }

        let (assoc_id, interface) = candidates[0];
        let _ = check_generics_prohibited(assoc_id, segment, gcx);
        Ty::new(
            TyKind::Alias {
                kind: AliasKind::Projection,
                def_id: assoc_id,
                args: interface.arguments,
            },
            gcx,
        )
    }

    fn collect_projection_candidates(
        &self,
        root: InterfaceReference<'ctx>,
        name: Symbol,
        out: &mut Vec<(DefinitionID, InterfaceReference<'ctx>)>,
    ) {
        let gcx = self.gcx();
        let mut queue = VecDeque::new();
        let mut seen: FxHashSet<InterfaceReference<'ctx>> = FxHashSet::default();

        if seen.insert(root) {
            queue.push_back(root);
        }

        while let Some(current) = queue.pop_front() {
            let Some(def) = self.interface_definition(current.id) else {
                continue;
            };

            if let Some(&assoc_id) = def.assoc_types.get(&name) {
                out.push((assoc_id, current));
            }

            for superface in &def.superfaces {
                let iface =
                    instantiate_interface_ref_with_args(gcx, superface.value, current.arguments);
                if seen.insert(iface) {
                    queue.push_back(iface);
                }
            }
        }
    }

    fn interface_definition(
        &self,
        interface_id: DefinitionID,
    ) -> Option<&'ctx InterfaceDefinition<'ctx>> {
        self.gcx().with_type_database(interface_id.package(), |db| {
            db.def_to_iface_def.get(&interface_id).copied()
        })
    }

    fn constraints_in_scope(
        &self,
        def_id: DefinitionID,
    ) -> Vec<crate::span::Spanned<Constraint<'ctx>>> {
        let gcx = self.gcx();
        let mut constraints = gcx.constraints_of(def_id);
        if let Some(parent) = gcx.definition_parent(def_id) {
            constraints.extend(self.constraints_in_scope(parent));
        }
        constraints
    }

    /// Resolve a type alias with cycle detection (no instantiation).
    fn resolve_alias(&self, alias_id: DefinitionID) -> Ty<'ctx> {
        let gcx = self.gcx();

        if let Some(cached) = gcx.try_get_alias_type(alias_id) {
            return cached;
        }

        let Some(def) = gcx.with_type_database(alias_id.package(), |db| {
            db.alias_table.aliases.get(&alias_id).cloned()
        }) else {
            let name = gcx.definition_ident(alias_id).symbol;
            gcx.dcx().emit_error(
                format!("unknown type alias '{}'", name.as_str()).into(),
                None,
            );
            return gcx.types.error;
        };

        if let Err(cycle) = LOWERING_REQUEST.with(|req| req.enter_alias(alias_id)) {
            let mut cycle_display: Vec<_> = cycle
                .iter()
                .map(|id| gcx.definition_ident(*id).symbol.as_str().to_string())
                .collect();
            if let Some(first) = cycle_display.first().cloned() {
                cycle_display.push(first);
            }
            let message = format!(
                "circular type alias\n\tcycle: {}",
                cycle_display.join(" -> ")
            );
            gcx.dcx().emit_error(message, Some(def.span));
            gcx.cache_alias_type(alias_id, gcx.types.error);
            return gcx.types.error;
        }

        let lowered = self.lower_type(&def.ast_ty);
        LOWERING_REQUEST.with(|req| req.exit_alias(alias_id));

        gcx.cache_alias_type(alias_id, lowered);

        lowered
    }

    pub fn lower_array_length(&self, anon: &hir::AnonConst) -> Const<'ctx> {
        if let Some(param) = self.lower_const_parameter(anon) {
            return param;
        }

        let gcx = self.gcx();
        let Some(value) = eval_const_expression(gcx, &anon.value) else {
            return self.error_const();
        };

        let len = match value {
            ConstValue::Integer(i) if i >= 0 => i,
            ConstValue::Integer(_) => {
                gcx.dcx().emit_error(
                    "array length must be non-negative".into(),
                    Some(anon.value.span),
                );
                return self.error_const();
            }
            _ => {
                gcx.dcx().emit_error(
                    "array length must be an integer constant".into(),
                    Some(anon.value.span),
                );
                return self.error_const();
            }
        };

        Const {
            ty: gcx.types.uint,
            kind: ConstKind::Value(ConstValue::Integer(len)),
        }
    }

    fn lower_const_parameter(&self, anon: &hir::AnonConst) -> Option<Const<'ctx>> {
        let hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path)) = &anon.value.kind else {
            return None;
        };

        let hir::Resolution::Definition(
            param_id,
            crate::sema::resolve::models::DefinitionKind::ConstParameter,
        ) = path.resolution
        else {
            return None;
        };

        let gcx = self.gcx();
        let owner = gcx.definition_parent(param_id)?;
        let generics = gcx.generics_of(owner);
        let def = generics.parameters.iter().find(|p| p.id == param_id)?;

        let ty = match &def.kind {
            GenericParameterDefinitionKind::Const { ty, .. } => self.lower_type(ty),
            _ => return None,
        };

        let param = GenericParameter {
            index: def.index,
            name: def.name,
        };

        Some(Const {
            ty,
            kind: ConstKind::Param(param),
        })
    }

    fn const_param_from_type_arg(&self, ty: &hir::Type) -> Option<Const<'ctx>> {
        let hir::TypeKind::Nominal(hir::ResolvedPath::Resolved(path)) = &ty.kind else {
            return None;
        };

        let hir::Resolution::Definition(param_id, DefinitionKind::ConstParameter) = path.resolution
        else {
            return None;
        };

        let gcx = self.gcx();
        let owner = gcx.definition_parent(param_id)?;
        let generics = gcx.generics_of(owner);
        let def = generics.parameters.iter().find(|p| p.id == param_id)?;

        let GenericParameterDefinitionKind::Const { ty, .. } = &def.kind else {
            return None;
        };

        let param = GenericParameter {
            index: def.index,
            name: def.name,
        };

        Some(Const {
            ty: self.lower_type(ty),
            kind: ConstKind::Param(param),
        })
    }

    fn lower_foundation_type(&self, path: &hir::Path, decl: hir::StdType) -> Option<Ty<'ctx>> {
        let gcx = self.gcx();
        let name = decl.name_str()?;
        let def_id = match gcx.find_std_type(name) {
            Some(id) => id,
            None => {
                gcx.dcx().emit_error(
                    format!("unable to resolve std type '{name}'"),
                    Some(path.span),
                );
                return None;
            }
        };
        let segment = path.segments.last().unwrap();
        let args = self.lower_type_arguments(def_id, segment);

        Some(instantiate_ty_with_args(gcx, gcx.get_type(def_id), args))
    }
}

fn const_value_matches_type(value: ConstValue, ty: Ty<'_>) -> bool {
    match ty.kind() {
        TyKind::Error => true,
        TyKind::Bool => matches!(value, ConstValue::Bool(_)),
        TyKind::Rune => matches!(value, ConstValue::Rune(_)),
        TyKind::String => matches!(value, ConstValue::String(_)),
        TyKind::Int(_) | TyKind::UInt(_) => matches!(value, ConstValue::Integer(_)),
        TyKind::Float(_) => matches!(value, ConstValue::Float(_)),
        TyKind::Tuple(items) => items.is_empty() && matches!(value, ConstValue::Unit),
        _ => false,
    }
}

fn check_generics_prohibited(
    def_id: DefinitionID,
    segment: &hir::PathSegment,
    context: GlobalContext<'_>,
) -> bool {
    let kind = context.definition_kind(def_id);

    let Some(arguments) = &segment.arguments else {
        return true;
    };
    // No type arguments => always OK
    if arguments.arguments.is_empty() {
        return true;
    }

    // Only these kinds allow generics
    let allowed = matches!(
        kind,
        DefinitionKind::Struct
            | DefinitionKind::Enum
            | DefinitionKind::Interface
            | DefinitionKind::TypeAlias
            | DefinitionKind::Function
    );

    if !allowed {
        context.dcx.emit_error(
            format!("Generics not permitted on {:?}", kind),
            Some(arguments.span),
        );
        return false;
    }

    true
}

pub fn check_generic_arg_count(
    id: DefinitionID,
    segment: &hir::PathSegment,
    context: GlobalContext<'_>,
) -> bool {
    let generics = context.generics_of(id);
    let should_infer = segment.arguments.is_none();

    let defaults_count = generics.default_count();
    let total_count = generics.total_count();
    let owns_self = generics.has_self && generics.parent_count == 0;

    let min = if !should_infer {
        total_count
            .saturating_sub(defaults_count)
            .saturating_sub(owns_self as usize)
    } else {
        0
    };

    let provided = segment
        .arguments
        .as_ref()
        .map(|v| {
            v.arguments
                .iter()
                .filter(|arg| !matches!(arg, crate::hir::TypeArgument::AssociatedType(..)))
                .count()
        })
        .unwrap_or(0);

    if matches!(context.definition_kind(id), DefinitionKind::Function) {
        // any number ≤ total is OK – inference will fill the rest
        if provided <= total_count {
            return true;
        }
        context.dcx().emit_error(
            format!(
                "excess generic arguments: function takes at most {total_count}, provided {provided}"
            ),
            segment.arguments.as_ref().map(|v| v.span),
        );
        return false;
    }

    if (min..=total_count).contains(&provided) {
        return true;
    }

    if provided > total_count {
        if total_count == 0 {
            let message = format!(
                "'{}' does not accept generic arguments",
                segment.identifier.symbol.as_str()
            );
            context
                .dcx()
                .emit_error(message, segment.arguments.as_ref().map(|v| v.span));
        } else {
            let message = format!(
                "excess generic arguments, '{}' requires {} type argument(s), provided {}",
                segment.identifier.symbol, min, provided
            );
            context
                .dcx()
                .emit_error(message, segment.arguments.as_ref().map(|v| v.span));
        }
    } else {
        context.dcx().emit_error(
            "Missing Generic Arguments".into(),
            Some(segment.identifier.span),
        );
    }

    return false;
}

fn check_no_type_arguments(
    segment: &hir::PathSegment,
    context: GlobalContext<'_>,
    message: String,
) -> bool {
    let Some(arguments) = &segment.arguments else {
        return true;
    };

    context.dcx.emit_error(message.into(), Some(arguments.span));
    false
}
