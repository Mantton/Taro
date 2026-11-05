//! Source-level restrictions on the initialized handle used by convenience init.
//! Field operations are allowed after delegation; self itself cannot escape,
//! be replaced, be captured, or invoke instance methods during construction.
use super::*;
use crate::sema::{models::TyKind, tycheck::solve::Adjustment};
use rustc_hash::{FxHashMap, FxHashSet};

#[cfg(test)]
mod tests {
    #[test]
    fn g36_convenience_initializers_reject_field_references() {
        for expression in [
            "&self.value",
            "&self.nested.value",
            "&self.pair.0",
            "self.value.exposed()",
        ] {
            let source = format!(
                "struct Nested {{ value: int32 }}\nclass Record {{ value: int32 = 1; nested: Nested = Nested {{ value: 2 }}; pair: (int32, int32) = (3, 4) }}\nextend Record {{ init(_ flag: bool) {{}}; convenience init() {{ self.init(true); save({expression}) }}; }}\nfunc save(_ value: &int32) {{}}\ninterface Exposed {{ func exposed() -> &int32; }}\nconform &int32 to Exposed {{ func exposed() -> &int32 {{ self }}; }}\nfunc main() {{}}"
            );
            let diagnostics = crate::test_support::analyze_script_diagnostics(&source);
            assert!(
                diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.message.contains(
                        "cannot take references to self or its fields during initialization"
                    )),
                "{expression}: {diagnostics:#?}"
            );
        }
    }

    #[test]
    fn g36_convenience_initializers_can_reference_copies_and_independent_pointees() {
        crate::test_support::analyze_script(
            "class Record { value: &int32; other: &int32 }\nextend Record { init(_ value: &int32) { self.value = value; self.other = value }; convenience init() { local := 7; self.init(&local); self.other = &*self.value; copied := *self.value; save(&copied) }; }\nfunc save(_ value: &int32) {}\nfunc main() {}",
            |_, _| {},
        );
    }
}

pub(super) fn validate<'ctx>(
    package: &hir::Package,
    context: Gcx<'ctx>,
    results: &TypeCheckResults<'ctx>,
) {
    struct Initializers<'a, 'ctx> {
        context: Gcx<'ctx>,
        results: &'a TypeCheckResults<'ctx>,
        edges: FxHashMap<DefinitionID, Vec<DefinitionID>>,
        propagated: FxHashSet<hir::NodeID>,
    }
    impl<'ctx> HirVisitor for Initializers<'_, 'ctx> {
        fn visit_expression(&mut self, expression: &hir::Expression) {
            if let hir::ExpressionKind::Propagate(inner) = &expression.kind {
                self.propagated.insert(inner.id);
            }
            if (self.results.base_initializer_calls.contains(&expression.id)
                || self.results.self_initializer_calls.contains(&expression.id))
                && let hir::ExpressionKind::MethodCall { receiver, .. } = &expression.kind
            {
                let source = self
                    .results
                    .overload_source(receiver.id)
                    .or_else(|| self.results.overload_source(expression.id))
                    .or_else(|| {
                        self.results
                            .value_resolution(receiver.id)
                            .and_then(|value| value.definition_id())
                    });
                if self
                    .context
                    .result_parts(self.results.node_type(expression.id))
                    .is_some()
                    && !self.propagated.contains(&expression.id)
                {
                    self.context.dcx().emit_error("fallible initializer delegation must propagate its error immediately with !".into(), Some(expression.span));
                }
                let entry = source.and_then(|source| {
                    self.context
                        .class_initializer(self.context.get_signature(source).output, source)
                });
                if entry.is_none() {
                    self.context.dcx().emit_error(
                        "delegation must select a class initializer".into(),
                        Some(expression.span),
                    );
                } else if self.results.base_initializer_calls.contains(&expression.id)
                    && entry.unwrap().is_convenience
                {
                    self.context.dcx().emit_error(
                        "super.init must select a designated initializer".into(),
                        Some(expression.span),
                    );
                }
            }
            hir::walk_expression(self, expression);
        }
        fn visit_function(
            &mut self,
            id: DefinitionID,
            node: &hir::Function,
            fc: hir::FunctionContext,
        ) {
            if node
                .initializer_kind
                .is_some_and(|kind| kind.is_convenience)
            {
                let class = self.context.initializer_target(id);
                if !self.context.is_class_type(class) {
                    self.context.dcx().emit_error(
                        "convenience init requires a class".into(),
                        Some(node.signature.span),
                    );
                    return;
                }
                let hir::StatementKind::Variable(local) =
                    &node.block.as_ref().unwrap().statements[0].kind
                else {
                    unreachable!()
                };
                let mut checker = Body {
                    context: self.context,
                    results: self.results,
                    binding: local.pattern.id,
                    fallible: self
                        .context
                        .result_parts(self.context.get_signature(id).output)
                        .is_some(),
                    closures: 0,
                    edges: vec![],
                };
                hir::walk_function(&mut checker, id, node, fc);
                self.edges.insert(id, checker.edges);
            }
            hir::walk_function(self, id, node, fc);
        }
    }
    struct Body<'a, 'ctx> {
        context: Gcx<'ctx>,
        results: &'a TypeCheckResults<'ctx>,
        binding: hir::NodeID,
        fallible: bool,
        closures: usize,
        edges: Vec<DefinitionID>,
    }
    impl Body<'_, '_> {
        fn is_self(&self, expression: &hir::Expression) -> bool {
            matches!(&expression.kind, hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path))
                if matches!(path.resolution, hir::Resolution::LocalVariable(id) if id == self.binding))
        }
        fn reject(&self, expression: &hir::Expression) {
            self.context.dcx().emit_error("cannot copy, capture, pass, or replace self or invoke instance methods during convenience initialization; access stored fields instead".into(), Some(expression.span));
        }

        // Convenience self is already a class handle, so its field addresses
        // do not use ConstructorSelf MIR storage. Enforce the same source rule
        // here. Following a stored pointer, reference or class handle selects
        // independent storage; projecting through a value field does not.
        fn self_storage(&self, expression: &hir::Expression) -> bool {
            let expression = self
                .results
                .selected_brackets
                .get(&expression.id)
                .unwrap_or(expression);
            if self.is_self(expression) {
                return true;
            }
            let inline = |target: &hir::Expression| {
                self.self_storage(target)
                    && self.results.try_node_type(target.id).is_some_and(|ty| {
                        !self.context.is_class_type(ty)
                            && !matches!(ty.kind(), TyKind::Reference(_) | TyKind::Pointer(..))
                    })
            };
            match &expression.kind {
                hir::ExpressionKind::Member { target, .. }
                    if self.results.field_index(expression.id).is_some() =>
                {
                    self.is_self(target) || inline(target)
                }
                hir::ExpressionKind::TupleAccess(target, _) => inline(target),
                hir::ExpressionKind::Index { target, .. }
                    if self
                        .results
                        .try_node_type(target.id)
                        .is_some_and(|ty| matches!(ty.kind(), TyKind::Array { .. })) =>
                {
                    inline(target)
                }
                _ => false,
            }
        }
    }
    impl HirVisitor for Body<'_, '_> {
        fn visit_expression(&mut self, expression: &hir::Expression) {
            // Inspect the typed indexing/specialization branch, whose field
            // identities and receiver adjustments differ from the parse fork.
            let expression = self
                .results
                .selected_brackets
                .get(&expression.id)
                .unwrap_or(expression);
            if self.fallible
                && self.closures == 0
                && let hir::ExpressionKind::Return { value: Some(value) } = &expression.kind
            {
                let definition = if let hir::ExpressionKind::Call { callee, .. } = &value.kind {
                    self.results
                        .overload_source(callee.id)
                        .or_else(|| {
                            self.results
                                .value_resolution(callee.id)
                                .and_then(|value| value.definition_id())
                        })
                        .or_else(|| match &callee.kind {
                            hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path)) => {
                                path.resolution.definition_id()
                            }
                            _ => None,
                        })
                } else {
                    None
                };
                if definition.is_none()
                    || definition != self.context.std_item_def(hir::StdItem::ResultErrCtor)
                {
                    self.context.dcx().emit_error("fallible convenience init returns initialized self automatically; use a bare return for success or return .err(error) for failure".into(), Some(expression.span));
                }
            }
            let explicit = matches!(&expression.kind,
                hir::ExpressionKind::Reference(target) if self.self_storage(target));
            let implicit = self.self_storage(expression)
                && self
                    .results
                    .node_adjustments(expression.id)
                    .is_some_and(|adjustments| {
                        adjustments
                            .iter()
                            .any(|adjustment| matches!(adjustment, Adjustment::Reference))
                            && !adjustments
                                .iter()
                                .any(|adjustment| matches!(adjustment, Adjustment::Dereference))
                    });
            if explicit || implicit {
                self.context.dcx().emit_error(
                    "cannot take references to self or its fields during initialization".into(),
                    Some(expression.span),
                );
                return;
            }
            if self.is_self(expression) {
                self.reject(expression);
                return;
            }
            match &expression.kind {
                hir::ExpressionKind::Member { target, .. } if self.is_self(target) => {
                    if self.closures != 0
                        || self.results.field_index(expression.id).is_none()
                        || self.results.property_read(expression.id).is_some()
                        || self
                            .results
                            .node_adjustments(target.id)
                            .is_some_and(|adjustments| {
                                adjustments.iter().any(|adjustment| {
                                    matches!(adjustment, Adjustment::DerefCall { .. })
                                })
                            })
                    {
                        self.reject(expression);
                    }
                    return;
                }
                hir::ExpressionKind::MethodCall {
                    receiver,
                    arguments,
                    ..
                } if self.results.self_initializer_calls.contains(&expression.id) => {
                    if self.closures != 0 {
                        self.reject(expression);
                    }
                    let source = self
                        .results
                        .overload_source(receiver.id)
                        .or_else(|| self.results.overload_source(expression.id))
                        .or_else(|| {
                            self.results
                                .value_resolution(receiver.id)
                                .and_then(|value| value.definition_id())
                        });
                    if let Some(source) = source {
                        self.edges.push(source);
                    }
                    for argument in arguments {
                        self.visit_expression(&argument.expression);
                    }
                    return;
                }
                hir::ExpressionKind::Closure(_) => {
                    self.closures += 1;
                    hir::walk_expression(self, expression);
                    self.closures -= 1;
                    return;
                }
                hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path))
                    if path.segments.len() == 1
                        && path.segments[0].identifier.symbol.as_str() == "super" =>
                {
                    self.reject(expression);
                    return;
                }
                _ => {}
            }
            hir::walk_expression(self, expression);
        }
    }
    let mut initializers = Initializers {
        context,
        results,
        edges: FxHashMap::default(),
        propagated: FxHashSet::default(),
    };
    hir::walk_package(&mut initializers, package);
    // Persist direct source facts before traversing actual subclass contexts.
    // Imported base convenience bodies must participate even without source HIR.
    let classes = context.with_session_type_database(|database| {
        database
            .def_to_struct_def
            .iter()
            .filter(|(_, definition)| definition.class_info.is_some())
            .map(|(id, definition)| (*id, (*definition).clone()))
            .collect::<Vec<_>>()
    });
    for (id, mut definition) in classes {
        let mut info = definition.class_info.unwrap();
        let entries: Vec<_> = info
            .initializers
            .iter()
            .map(|entry| {
                let mut entry = *entry;
                if !entry.is_inherited {
                    entry.delegations = context.store.arenas.global.alloc_slice_copy(
                        initializers
                            .edges
                            .get(&entry.definition)
                            .map(Vec::as_slice)
                            .unwrap_or(&[]),
                    );
                }
                entry
            })
            .collect();
        info.initializers = context.store.arenas.global.alloc_slice_copy(&entries);
        definition.class_info = Some(info);
        context.cache_struct_definition(id, definition);
    }
    fn origin(context: Gcx<'_>, mut id: DefinitionID) -> DefinitionID {
        loop {
            let inherited = context.store.synthetic_definitions.borrow().get(&id).and_then(|definition| {
                if let crate::sema::models::SyntheticDefinitionKind::InheritedClassInitializer { initializer, .. } = definition.kind { Some(initializer) } else { None }
            });
            match inherited {
                Some(source) => id = source,
                None => return id,
            }
        }
    }
    fn visit<'ctx>(
        context: Gcx<'ctx>,
        class: crate::sema::models::Ty<'ctx>,
        id: DefinitionID,
        active: &mut FxHashSet<DefinitionID>,
        done: &mut FxHashSet<DefinitionID>,
    ) -> bool {
        let id = origin(context, id);
        if done.contains(&id) {
            return false;
        }
        if !active.insert(id) {
            return true;
        }
        let source_class = context.initializer_target(id);
        let entry = context
            .class_initializer(source_class, id)
            .expect("source constructor");
        for &target in entry.delegations {
            let target_class = context.initializer_target(target);
            let target = context
                .class_initializer(target_class, target)
                .expect("delegation constructor");
            // Convenience-to-convenience calls keep their statically selected
            // body. Designated delegation resolves the requested subclass family.
            let next = if target.is_convenience {
                Some(target)
            } else {
                context.class_initializer(class, target.family)
            };
            if let Some(next) = next
                && next.is_convenience
                && visit(context, class, next.definition, active, done)
            {
                return true;
            }
        }
        active.remove(&id);
        done.insert(id);
        false
    }
    let classes = context.with_session_type_database(|database| {
        database
            .def_to_struct_def
            .iter()
            .filter(|(_, definition)| definition.class_info.is_some())
            .map(|(id, _)| *id)
            .collect::<Vec<_>>()
    });
    for id in classes {
        let class = context.get_type(id);
        let mut done = FxHashSet::default();
        for entry in context
            .class_info(class)
            .unwrap()
            .initializers
            .iter()
            .filter(|entry| entry.is_convenience)
        {
            if visit(
                context,
                class,
                entry.definition,
                &mut FxHashSet::default(),
                &mut done,
            ) {
                context.dcx().emit_error(
                    "convenience initializer delegation cycle in this class's constructor families"
                        .into(),
                    Some(context.definition_ident(entry.definition).span),
                );
            }
        }
    }
}
