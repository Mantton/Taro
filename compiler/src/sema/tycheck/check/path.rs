use super::*;

impl<'ctx> Checker<'ctx> {
    pub(super) fn is_unsafe_callable_definition(&self, id: DefinitionID) -> bool {
        self.gcx().definition_is_unsafe(id)
    }

    pub(super) fn emit_unsafe_callable_value_error(
        &self,
        def_id: DefinitionID,
        span: Span,
    ) -> Ty<'ctx> {
        self.gcx().dcx().emit_error(
            crate::sema::error::TypeError::UnsafeCallableValueNotAllowed {
                name: self.gcx().definition_symbol_or_fallback(def_id),
            }
            .format(self.gcx())
            .into(),
            Some(span),
        );
        Ty::error(self.gcx())
    }

    pub(super) fn resolve_callee(
        &self,
        node: &hir::Expression,
        cs: &Cs<'ctx>,
    ) -> Option<DefinitionID> {
        match &node.kind {
            hir::ExpressionKind::Path(path) => {
                if let Some(resolution) = self.results.borrow().value_resolution(node.id) {
                    return self.resolve_resolution_callee(&resolution);
                }
                let resolution = self.resolve_value_path_resolution(path, node.span, false, cs);
                self.resolve_resolution_callee(&resolution)
            }
            _ => None,
        }
    }

    pub(super) fn resolve_resolution_callee(&self, res: &hir::Resolution) -> Option<DefinitionID> {
        match res {
            hir::Resolution::Definition(id, DefinitionKind::Function)
            | hir::Resolution::Definition(id, DefinitionKind::AssociatedFunction)
            | hir::Resolution::Definition(id, DefinitionKind::VariantConstructor(..)) => Some(*id),
            _ => None,
        }
    }

    pub(super) fn resolve_value_path_resolution(
        &self,
        path: &hir::ResolvedPath,
        span: Span,
        emit_errors: bool,
        cs: &Cs<'ctx>,
    ) -> hir::Resolution {
        self.resolve_value_path_resolution_with_args(path, span, emit_errors, cs)
            .0
    }

    pub(super) fn resolve_value_path_resolution_with_args(
        &self,
        path: &hir::ResolvedPath,
        span: Span,
        emit_errors: bool,
        cs: &Cs<'ctx>,
    ) -> (
        hir::Resolution,
        Option<crate::sema::models::GenericArguments<'ctx>>,
    ) {
        match path {
            hir::ResolvedPath::Resolved(path) => {
                if let hir::Resolution::Definition(property_id, DefinitionKind::AssociatedProperty) =
                    path.resolution
                    && let Some(interface_id) = self.gcx().definition_parent(property_id)
                    && self.gcx().definition_kind(interface_id) == DefinitionKind::Interface
                    && let Some(requirements) = self.gcx().get_interface_requirements(interface_id)
                    && let Some(property) = requirements
                        .properties
                        .iter()
                        .find(|property| property.id == property_id)
                {
                    let mut accessors = vec![property.getter_id];
                    if let Some(setter_id) = property.setter_id {
                        accessors.push(setter_id);
                    }
                    (hir::Resolution::FunctionSet(accessors), None)
                } else {
                    (path.resolution.clone(), None)
                }
            }
            hir::ResolvedPath::Relative(base_ty, segment) => {
                // Attempt to reuse generic arguments from the base type for inherent
                // static members (e.g., `List[Int].new`). Avoid lowering interface
                // types without a provided `Self`, which would panic.
                let base_is_interface = matches!(
                    &base_ty.kind,
                    hir::TypeKind::Nominal(hir::ResolvedPath::Resolved(path))
                        if matches!(
                            path.resolution,
                            hir::Resolution::Definition(_, DefinitionKind::Interface)
                        )
                );

                let mut lowered_base_ty = None;
                let mut base_args = None;
                if !base_is_interface {
                    let ty = self.lower_type(base_ty);
                    let ty = cs.infer_cx.resolve_vars_if_possible(ty);
                    if let TyKind::Adt(_, args) = ty.kind() {
                        if !args.is_empty() {
                            base_args = Some(args);
                        }
                    }
                    lowered_base_ty = Some(ty);
                }

                if !matches!(segment.resolution, hir::Resolution::Error) {
                    if let hir::Resolution::Definition(
                        property_id,
                        DefinitionKind::AssociatedProperty,
                    ) = segment.resolution
                        && let Some(interface_id) = self.gcx().definition_parent(property_id)
                        && self.gcx().definition_kind(interface_id) == DefinitionKind::Interface
                        && let Some(requirements) =
                            self.gcx().get_interface_requirements(interface_id)
                        && let Some(property) = requirements
                            .properties
                            .iter()
                            .find(|property| property.id == property_id)
                    {
                        let mut accessors = vec![property.getter_id];
                        if let Some(setter_id) = property.setter_id {
                            accessors.push(setter_id);
                        }
                        return (hir::Resolution::FunctionSet(accessors), base_args);
                    }
                    return (segment.resolution.clone(), base_args);
                }

                let base_ty = match lowered_base_ty {
                    Some(ty) => ty,
                    None => {
                        if emit_errors {
                            self.gcx().dcx().emit_error(
                                "cannot resolve members on this type receiver".into(),
                                Some(span),
                            );
                        }
                        return (hir::Resolution::Error, None);
                    }
                };

                let Some(head) = type_head_from_value_ty(base_ty) else {
                    let resolution = self.resolve_bounded_static_member_resolution(
                        base_ty,
                        &segment.identifier,
                        segment.identifier.span,
                        emit_errors,
                    );
                    return (resolution, base_args);
                };

                let resolution = self.resolve_static_member_resolution(
                    head,
                    base_ty,
                    &segment.identifier,
                    segment.identifier.span,
                    emit_errors,
                );
                (resolution, base_args)
            }
        }
    }

    pub(super) fn record_value_path_resolution(
        &self,
        node_id: NodeID,
        resolution: &hir::Resolution,
    ) {
        match resolution {
            hir::Resolution::Definition(..)
            | hir::Resolution::LocalVariable(..)
            | hir::Resolution::StdItem(..) => {
                self.results
                    .borrow_mut()
                    .record_value_resolution(node_id, resolution.clone());
            }
            _ => {}
        }
    }

    pub(super) fn resolve_static_member_resolution(
        &self,
        head: TypeHead,
        base_ty: Ty<'ctx>,
        name: &crate::span::Identifier,
        span: Span,
        emit_errors: bool,
    ) -> hir::Resolution {
        let gcx = self.gcx();
        if let TypeHead::Nominal(def_id) = head {
            if gcx.definition_kind(def_id) == DefinitionKind::Enum {
                let enum_def = gcx.get_enum_definition(def_id);

                if let Some(variant) = enum_def.variants.iter().find(|v| v.name == name.symbol) {
                    if !gcx.is_definition_visible(variant.ctor_def_id, self.current_def) {
                        if emit_errors {
                            gcx.dcx()
                                .emit_error("enum variant is not visible here".into(), Some(span));
                        }
                        return hir::Resolution::Error;
                    }

                    let kind = gcx.definition_kind(variant.ctor_def_id);
                    return hir::Resolution::Definition(variant.ctor_def_id, kind);
                }
            }
        }

        let candidates = self.collect_static_member_candidates(head, name.symbol);

        if candidates.is_empty() {
            if emit_errors {
                let msg = format!(
                    "unknown associated symbol named '{}' on type '{}'",
                    gcx.symbol_text(name.symbol),
                    base_ty.format(gcx)
                );
                gcx.dcx().emit_error(msg.into(), Some(span));
            }
            return hir::Resolution::Error;
        }

        let visible: Vec<_> = candidates
            .iter()
            .cloned()
            .filter(|id| gcx.is_definition_visible(*id, self.current_def))
            .collect();

        if visible.is_empty() {
            if emit_errors {
                gcx.dcx().emit_error(
                    format!(
                        "static member '{}' is not visible here",
                        gcx.symbol_text(name.symbol)
                    )
                    .into(),
                    Some(span),
                );
            }
            return hir::Resolution::Error;
        }

        if visible.len() == 1 {
            let id = visible[0];
            let kind = gcx.definition_kind(id);
            return hir::Resolution::Definition(id, kind);
        }

        hir::Resolution::FunctionSet(visible)
    }

    pub(super) fn collect_static_member_candidates(
        &self,
        head: TypeHead,
        name: Symbol,
    ) -> Vec<DefinitionID> {
        let gcx = self.gcx();
        let databases = gcx.store.type_databases.borrow();
        let mut members = Vec::new();

        for db in databases.values() {
            if let Some(index) = db.type_head_to_members.get(&head) {
                if let Some(set) = index.inherent_static.get(&name) {
                    members.extend(set.members.iter().cloned());
                }
            }
        }

        if let TypeHead::Nominal(interface_id) = head
            && gcx.definition_kind(interface_id) == DefinitionKind::Interface
            && let Some(requirements) = gcx.get_interface_requirements(interface_id)
            && let Some(property) = requirements
                .properties
                .iter()
                .find(|property| property.name == name)
        {
            members.push(property.getter_id);
            if let Some(setter_id) = property.setter_id {
                members.push(setter_id);
            }
        }

        members
    }

    pub(super) fn resolve_bounded_static_member_resolution(
        &self,
        base_ty: Ty<'ctx>,
        name: &crate::span::Identifier,
        span: Span,
        emit_errors: bool,
    ) -> hir::Resolution {
        let gcx = self.gcx();
        let candidates = self.collect_bounded_static_member_candidates(base_ty, name.symbol);

        if candidates.is_empty() {
            if emit_errors {
                let msg = format!(
                    "unknown associated symbol named '{}' on type '{}'",
                    gcx.symbol_text(name.symbol),
                    base_ty.format(gcx)
                );
                gcx.dcx().emit_error(msg.into(), Some(span));
            }
            return hir::Resolution::Error;
        }

        let visible: Vec<_> = candidates
            .into_iter()
            .filter(|id| gcx.is_definition_visible(*id, self.current_def))
            .collect();
        if visible.is_empty() {
            if emit_errors {
                gcx.dcx().emit_error(
                    format!(
                        "static member '{}' is not visible here",
                        gcx.symbol_text(name.symbol)
                    )
                    .into(),
                    Some(span),
                );
            }
            return hir::Resolution::Error;
        }

        if visible.len() == 1 {
            let id = visible[0];
            let kind = gcx.definition_kind(id);
            return hir::Resolution::Definition(id, kind);
        }

        hir::Resolution::FunctionSet(visible)
    }

    pub(super) fn collect_bounded_static_member_candidates(
        &self,
        base_ty: Ty<'ctx>,
        name: Symbol,
    ) -> Vec<DefinitionID> {
        let gcx = self.gcx();
        let mut roots: Vec<InterfaceReference<'ctx>> = Vec::new();

        match base_ty.kind() {
            TyKind::Parameter(_) => {
                let constraints = crate::sema::tycheck::constraints::canonical_constraints_of(
                    gcx,
                    self.current_def,
                );
                for constraint in constraints {
                    if let crate::sema::models::Constraint::Bound { ty, interface } =
                        constraint.value
                    {
                        if ty == base_ty {
                            roots.push(interface);
                        }
                    }
                }
            }
            TyKind::BoxedExistential { interfaces } => roots.extend_from_slice(interfaces),
            _ => return Vec::new(),
        }

        let mut out = Vec::new();
        let mut seen_defs: FxHashSet<DefinitionID> = FxHashSet::default();
        let mut seen_ifaces: FxHashSet<InterfaceReference<'ctx>> = FxHashSet::default();
        let mut queue = std::collections::VecDeque::new();

        for root in roots {
            if seen_ifaces.insert(root) {
                queue.push_back(root);
            }
        }

        while let Some(interface_ref) = queue.pop_front() {
            if let Some(requirements) = gcx.get_interface_requirements(interface_ref.id) {
                for method in &requirements.methods {
                    if method.name == name && !method.has_self && seen_defs.insert(method.id) {
                        out.push(method.id);
                    }
                }
            }

            let Some(interface_def) = gcx.get_interface_definition(interface_ref.id) else {
                continue;
            };

            for superface in &interface_def.superfaces {
                let instantiated = instantiate_interface_ref_with_args(
                    gcx,
                    superface.value,
                    interface_ref.arguments,
                );
                if seen_ifaces.insert(instantiated) {
                    queue.push_back(instantiated);
                }
            }
        }

        out
    }

    pub(super) fn value_path_def_id(&self, resolution: &hir::Resolution) -> Option<DefinitionID> {
        match resolution {
            hir::Resolution::StdItem(std_type) => self.gcx().std_item_def(*std_type),
            _ => resolution.definition_id(),
        }
    }

    pub(super) fn lower_value_path_instantiation_args(
        &self,
        resolution: &hir::Resolution,
        segment: &hir::PathSegment,
        base_args: Option<GenericArguments<'ctx>>,
    ) -> Option<GenericArguments<'ctx>> {
        let gcx = self.gcx();
        let explicit_args = segment
            .arguments
            .as_ref()
            .map(|args| args.arguments.as_slice())
            .unwrap_or(&[]);
        let mut positional_args = Vec::with_capacity(explicit_args.len());
        let mut has_associated_type_binding = false;
        for arg in explicit_args {
            if let hir::TypeArgument::AssociatedType(ident, _) = arg {
                has_associated_type_binding = true;
                gcx.dcx().emit_error(
                    "associated type bindings are not allowed in value generic arguments".into(),
                    Some(ident.span),
                );
            } else {
                positional_args.push(arg);
            }
        }
        let has_explicit = segment.arguments.is_some();
        let args_span = segment
            .arguments
            .as_ref()
            .map(|args| args.span)
            .unwrap_or(segment.span);

        if let hir::Resolution::StdItem(std_type) = resolution {
            if std_type.name_str().is_none() {
                if has_explicit && (!has_associated_type_binding || !positional_args.is_empty()) {
                    gcx.dcx().emit_error(
                        "generic arguments are not permitted on this builtin".into(),
                        Some(args_span),
                    );
                }
                return None;
            }
        }

        match resolution {
            hir::Resolution::FunctionSet(_) => {
                if has_explicit && (!has_associated_type_binding || !positional_args.is_empty()) {
                    gcx.dcx().emit_error(
                        "generic arguments are not permitted on overloaded function sets".into(),
                        Some(args_span),
                    );
                }
                return base_args;
            }
            hir::Resolution::LocalVariable(_)
            | hir::Resolution::PrimaryType(_)
            | hir::Resolution::InterfaceSelfTypeParameter(_)
            | hir::Resolution::SelfTypeAlias(_)
            | hir::Resolution::Error => {
                if has_explicit && (!has_associated_type_binding || !positional_args.is_empty()) {
                    gcx.dcx().emit_error(
                        format!(
                            "generic arguments are not permitted on {}",
                            resolution.description()
                        )
                        .into(),
                        Some(args_span),
                    );
                }
                return None;
            }
            _ => {}
        }

        let Some(def_id) = self.value_path_def_id(resolution) else {
            return None;
        };

        let generics = gcx.generics_of(def_id);
        if generics.is_empty() && base_args.is_none() {
            if has_explicit && (!has_associated_type_binding || !positional_args.is_empty()) {
                let name = gcx.definition_ident(def_id).symbol;
                gcx.dcx().emit_error(
                    format!(
                        "'{}' does not accept generic arguments",
                        gcx.symbol_text(name)
                    )
                    .into(),
                    Some(args_span),
                );
            }
            return None;
        }

        let explicit_count = positional_args.len();
        let own_total = generics.total_count();
        let own_defaults = generics.default_count();
        let own_has_self = generics.has_self && generics.parent_count == 0;
        let def_kind = gcx.definition_kind(def_id);
        let allow_partial = matches!(
            def_kind,
            DefinitionKind::Function
                | DefinitionKind::AssociatedFunction
                | DefinitionKind::AssociatedOperator
                | DefinitionKind::VariantConstructor(VariantCtorKind::Function)
        );

        if !has_associated_type_binding && explicit_count > own_total {
            gcx.dcx().emit_error(
                format!(
                    "excess generic arguments: {} takes at most {}, provided {}",
                    def_kind.description(),
                    own_total,
                    explicit_count
                )
                .into(),
                Some(args_span),
            );
        } else if has_explicit && !has_associated_type_binding && !allow_partial {
            let min = own_total
                .saturating_sub(own_defaults)
                .saturating_sub(own_has_self as usize);
            if explicit_count < min {
                gcx.dcx().emit_error(
                    "Missing Generic Arguments".into(),
                    Some(segment.identifier.span),
                );
            }
        }

        let base_args = base_args.unwrap_or(GenericArguments::empty());
        let parent_count = if base_args.is_empty() {
            generics.parent_count
        } else {
            base_args.len()
        };
        let span = segment
            .arguments
            .as_ref()
            .map(|args| args.span)
            .unwrap_or(segment.span);
        let mut explicit_iter = positional_args.into_iter();

        let args = GenericsBuilder::for_item(gcx, def_id, |param, current_args| {
            let current_args = gcx.store.interners.intern_generic_args_slice(current_args);
            if param.index < parent_count {
                if let Some(arg) = base_args.get(param.index) {
                    return *arg;
                }
                return self.lower_value_path_missing_arg(param, span, current_args);
            }

            if let Some(arg) = explicit_iter.next() {
                return self.lower_value_path_explicit_arg(param, arg);
            }

            self.lower_value_path_missing_arg(param, span, current_args)
        });

        Some(args)
    }

    pub(super) fn lower_value_path_explicit_arg(
        &self,
        param: &GenericParameterDefinition,
        arg: &hir::TypeArgument,
    ) -> GenericArgument<'ctx> {
        let gcx = self.gcx();
        match (&param.kind, arg) {
            (GenericParameterDefinitionKind::Type { .. }, hir::TypeArgument::Type(ty)) => {
                GenericArgument::Type(self.lower_type(ty))
            }
            (GenericParameterDefinitionKind::Const { ty, .. }, hir::TypeArgument::Const(c)) => {
                let expected_ty = expected_const_param_ty(gcx, self.lowerer(), param)
                    .unwrap_or_else(|| self.lower_type(ty));
                GenericArgument::Const(self.lowerer().lower_const_argument(expected_ty, c))
            }
            (
                GenericParameterDefinitionKind::Type { .. },
                hir::TypeArgument::AssociatedType(ident, _),
            )
            | (
                GenericParameterDefinitionKind::Const { .. },
                hir::TypeArgument::AssociatedType(ident, _),
            ) => {
                gcx.dcx().emit_error(
                    "associated type bindings are not allowed in value generic arguments".into(),
                    Some(ident.span),
                );
                error_generic_argument(gcx, self.lowerer(), param)
            }
            (GenericParameterDefinitionKind::Type { .. }, hir::TypeArgument::Const(c)) => {
                gcx.dcx()
                    .emit_error("expected type argument".into(), Some(c.value.span));
                GenericArgument::Type(gcx.types.error)
            }
            (GenericParameterDefinitionKind::Const { ty, .. }, hir::TypeArgument::Type(ty_arg)) => {
                let expected_ty = expected_const_param_ty(gcx, self.lowerer(), param)
                    .unwrap_or_else(|| self.lower_type(ty));
                if let Some(param) = generic_const_param_from_type_arg(gcx, self.lowerer(), ty_arg)
                {
                    if const_arg_ty_mismatches(gcx, param.ty, expected_ty) {
                        emit_const_arg_type_mismatch(gcx, expected_ty, ty_arg.span);
                        return GenericArgument::Const(self.lowerer().error_const());
                    }
                    return GenericArgument::Const(Const {
                        ty: expected_ty,
                        kind: param.kind,
                    });
                }

                gcx.dcx()
                    .emit_error("expected const argument".into(), Some(ty_arg.span));
                GenericArgument::Const(self.lowerer().error_const())
            }
        }
    }

    pub(super) fn lower_value_path_missing_arg(
        &self,
        param: &GenericParameterDefinition,
        span: Span,
        current_args: GenericArguments<'ctx>,
    ) -> GenericArgument<'ctx> {
        let gcx = self.gcx();
        match &param.kind {
            GenericParameterDefinitionKind::Type { default } => {
                if let Some(default) = default {
                    if self.can_infer() {
                        let infer_ty = self.ty_infer(Some(param), span);
                        let mut default_ty = gcx
                            .try_generic_type_default(param.id)
                            .unwrap_or_else(|| self.lower_type(default));
                        default_ty = instantiate_ty_with_args(gcx, default_ty, current_args);
                        self.register_default_fallback(
                            crate::sema::tycheck::solve::DefaultFallbackGoalData {
                                infer_var: GenericArgument::Type(infer_ty),
                                default: GenericArgument::Type(default_ty),
                                span,
                            },
                        );
                        GenericArgument::Type(infer_ty)
                    } else {
                        GenericArgument::Type(
                            gcx.try_generic_type_default(param.id)
                                .unwrap_or_else(|| self.lower_type(default)),
                        )
                    }
                } else {
                    GenericArgument::Type(self.ty_infer(Some(param), span))
                }
            }
            GenericParameterDefinitionKind::Const { ty, default } => {
                let expected_ty = expected_const_param_ty(gcx, self.lowerer(), param)
                    .unwrap_or_else(|| self.lower_type(ty));
                if let Some(default) = default {
                    if self.can_infer() {
                        let infer_const = self.const_infer(expected_ty, Some(param), span);
                        let mut default_const =
                            gcx.try_generic_const_default(param.id).unwrap_or_else(|| {
                                self.lowerer().lower_const_argument(expected_ty, default)
                            });
                        default_const =
                            instantiate_const_with_args(gcx, default_const, current_args);
                        self.register_default_fallback(
                            crate::sema::tycheck::solve::DefaultFallbackGoalData {
                                infer_var: GenericArgument::Const(infer_const),
                                default: GenericArgument::Const(default_const),
                                span,
                            },
                        );
                        GenericArgument::Const(infer_const)
                    } else {
                        GenericArgument::Const(
                            gcx.try_generic_const_default(param.id).unwrap_or_else(|| {
                                self.lowerer().lower_const_argument(expected_ty, default)
                            }),
                        )
                    }
                } else {
                    if self.can_infer() {
                        GenericArgument::Const(self.const_infer(expected_ty, Some(param), span))
                    } else {
                        gcx.dcx()
                            .emit_error("missing const argument".into(), Some(span));
                        GenericArgument::Const(self.lowerer().error_const())
                    }
                }
            }
        }
    }

    pub(super) fn instantiate_value_path(
        &self,
        node_id: NodeID,
        span: Span,
        resolution: &hir::Resolution,
        instantiation_args: Option<GenericArguments<'ctx>>,
        expectation: Option<Ty<'ctx>>,
        allow_unsafe_callable_values: bool,
        prefer_async: Option<bool>,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        if matches!(resolution, hir::Resolution::Error) {
            return Ty::error(self.gcx());
        }

        let ty = self.synth_identifier_expression(
            node_id,
            span,
            resolution,
            expectation,
            instantiation_args,
            allow_unsafe_callable_values,
            prefer_async,
            cs,
        );

        if let Some(def_id) = self.value_path_def_id(resolution) {
            let generics = self.gcx().generics_of(def_id);
            if !generics.is_empty() {
                if let Some(args) = instantiation_args {
                    cs.record_instantiation(node_id, args);
                    cs.add_constraints_for_def_at_call(def_id, Some(args), span, node_id);
                    if ty.needs_instantiation() {
                        return instantiate_ty_with_args(self.gcx(), ty, args);
                    }
                    return ty;
                }

                if ty.needs_instantiation() {
                    let args = cs.infer_cx.fresh_args_for_def(def_id, span);
                    let instantiated = instantiate_ty_with_args(self.gcx(), ty, args);
                    cs.record_instantiation(node_id, args);
                    cs.add_constraints_for_def_at_call(def_id, Some(args), span, node_id);
                    return instantiated;
                }
            }
        }

        ty
    }
}
