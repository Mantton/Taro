use crate::find::ResolutionState;

use super::resolver::Resolver;
use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::hash_map::Entry;
use taroc_error::CompileResult;
use taroc_hir::{
    Declaration, DeclarationContext, DefinitionID, DefinitionKind, NodeID, Resolution,
    visitor::{self, HirVisitor},
};
use taroc_resolve_models::{
    LexicalScope, LexicalScopeSource, PathResult, PathSource, PatternSource, ResolutionError,
    Segment,
};
use taroc_span::{FileID, Identifier, Span, Spanned, Symbol};

pub fn run(package: &taroc_hir::Package, resolver: &mut Resolver) -> CompileResult<()> {
    let actor = Actor::new(resolver);
    actor.run(package);
    resolver.context.diagnostics.report()
}

pub struct GenericsCollector<'res, 'ctx> {
    pub resolver: &'res mut Resolver<'ctx>,
    pub parent: Option<DefinitionID>,
    pub table: FxHashMap<DefinitionID, Vec<(Symbol, DefinitionID)>>,
}

impl<'res, 'ctx> GenericsCollector<'res, 'ctx> {
    pub fn run(
        package: &taroc_hir::Package,
        resolver: &'res mut Resolver<'ctx>,
    ) -> CompileResult<()> {
        let mut actor = GenericsCollector {
            resolver,
            parent: None,
            table: Default::default(),
        };
        taroc_hir::visitor::walk_package(&mut actor, package);
        actor.resolver.generics_table = actor.table;
        actor.resolver.context.diagnostics.report()
    }
}

impl HirVisitor for GenericsCollector<'_, '_> {
    fn visit_declaration(
        &mut self,
        d: &taroc_hir::Declaration,
        c: DeclarationContext,
    ) -> Self::Result {
        let def_id = self.resolver.def_id(d.id);
        self.parent = Some(def_id);
        taroc_hir::visitor::walk_declaration(self, d, c);
    }

    fn visit_type_parameters(&mut self, t: &taroc_hir::TypeParameters) -> Self::Result {
        let params = &t.parameters;
        let parent = self.parent.unwrap();

        if params.is_empty() {
            return;
        }

        let mut items = vec![];
        let mut seen_bindings: FxHashMap<Symbol, Span> = Default::default();

        for param in params.iter() {
            let def_id = self.resolver.def_id(param.id);
            let kind = DefinitionKind::TypeParameter;
            let name = param.identifier.symbol.clone();
            let entry = seen_bindings.entry(name.clone());

            match entry {
                Entry::Occupied(_) => {
                    // param has already been defined
                    let msg = format!("TypeParameter '{name}' is already defined");
                    self.resolver
                        .context
                        .diagnostics
                        .error(msg, param.identifier.span);
                    continue;
                }
                Entry::Vacant(entry) => {
                    // mark as seen
                    entry.insert(param.identifier.span);
                }
            }

            items.push((name, def_id));
            let res = Resolution::Definition(def_id, kind);
            self.resolver.rescord_resolution(param.id, res);
        }

        self.table.insert(parent, items);
    }
}

struct Actor<'res, 'ctx> {
    pub resolver: &'res mut Resolver<'ctx>,
    pub scopes: Vec<LexicalScope<'ctx>>,
    pub current_file: Option<FileID>,
}

impl Actor<'_, '_> {
    fn new<'res, 'ctx>(resolver: &'res mut Resolver<'ctx>) -> Actor<'res, 'ctx> {
        Actor {
            resolver,
            scopes: Default::default(),
            current_file: None,
        }
    }

    fn run(mut self, package: &taroc_hir::Package) {
        taroc_hir::visitor::walk_package(&mut self, package);
        assert!(self.scopes.is_empty(), "no hanging scopes")
    }
}

impl<'res, 'ctx> Actor<'res, 'ctx> {
    fn with_scope<T>(
        &mut self,
        source: LexicalScopeSource<'ctx>,
        work: impl FnOnce(&mut Self) -> T,
    ) -> T {
        self.scopes.push(LexicalScope::new(source));
        let result = work(self);
        self.scopes.pop();
        result
    }

    fn with_generics_scope(&mut self, id: DefinitionID, work: impl FnOnce(&mut Self)) {
        let generics = if id.is_local(self.resolver.session().package_index) {
            self.resolver.generics_table.get(&id).cloned()
        } else {
            self.resolver.context.resolution_generics(id)
        };

        let Some(generics) = generics else {
            work(self);
            return;
        };

        let mut scope = LexicalScope::new(LexicalScopeSource::Plain);
        for (symbol, id) in generics.into_iter() {
            scope.define(
                symbol,
                Resolution::Definition(id, DefinitionKind::TypeParameter),
            );
        }

        self.scopes.push(scope);
        work(self);
        self.scopes.pop();
    }

    fn with_self_alias_scope(&mut self, self_res: Resolution, work: impl FnOnce(&mut Self)) {
        let mut scope = LexicalScope::new(LexicalScopeSource::Plain);
        scope.define(Symbol::with("Self"), self_res);
        self.scopes.push(scope);
        work(self);
        self.scopes.pop();
    }
}

impl HirVisitor for Actor<'_, '_> {
    fn visit_module(&mut self, module: &taroc_hir::Module) -> Self::Result {
        // Soft Reset on Modular Level, So Module Root is Scope Count
        let previous = std::mem::take(&mut self.scopes);
        self.scopes = vec![];

        let module_id = self.resolver.def_id(module.id);
        let context = self
            .resolver
            .get_context(&module_id)
            .expect("modules must always have a definition context");

        self.with_scope(LexicalScopeSource::Context(context), |this| {
            taroc_hir::visitor::walk_module(this, module)
        });
        self.scopes = previous;
    }

    fn visit_file(&mut self, file: &taroc_hir::File) -> Self::Result {
        // File
        let context = self.resolver.get_file_context(&file.id);
        self.current_file = Some(file.id);

        // Visit
        self.with_scope(LexicalScopeSource::Context(context), |this| {
            taroc_hir::visitor::walk_file(this, file)
        })
    }

    fn visit_block(&mut self, b: &taroc_hir::Block) -> Self::Result {
        self.resolve_block(b);
    }

    fn visit_declaration(
        &mut self,
        d: &taroc_hir::Declaration,
        c: DeclarationContext,
    ) -> Self::Result {
        self.resolve_declaration(d, c);
    }

    fn visit_type(&mut self, ty: &taroc_hir::Type) -> Self::Result {
        match &ty.kind {
            taroc_hir::TypeKind::Path(path) => {
                self.resolve_path_with_source(ty.id, path, PathSource::Type);
            }
            _ => {}
        }
        taroc_hir::visitor::walk_type(self, ty);
    }

    fn visit_generic_requirement(&mut self, n: &taroc_hir::GenericRequirement) -> Self::Result {
        match n {
            taroc_hir::GenericRequirement::SameTypeRequirement(c) => {
                self.resolve_path_with_source(
                    c.bounded_type.id,
                    &c.bounded_type.path,
                    PathSource::Type,
                );
                self.visit_type(&c.bound);
            }
            taroc_hir::GenericRequirement::ConformanceRequirement(c) => {
                self.resolve_path_with_source(
                    c.bounded_type.id,
                    &c.bounded_type.path,
                    PathSource::Type,
                );
                self.visit_generic_bounds(&c.bounds);
            }
        }
    }

    fn visit_generic_bound(&mut self, n: &taroc_hir::GenericBound) -> Self::Result {
        self.resolve_path_with_source(n.path.id, &n.path.path, PathSource::Interface);
    }

    fn visit_expression(&mut self, e: &taroc_hir::Expression) -> Self::Result {
        self.resolve_expression(e);
    }

    fn visit_local(&mut self, l: &taroc_hir::Local) -> Self::Result {
        self.resolve_local(l);
    }

    fn visit_function(&mut self, f: &taroc_hir::Function) -> Self::Result {
        if let Some(body) = &f.block {
            self.with_scope(LexicalScopeSource::Function, |this| {
                this.visit_generics(&f.generics);
                this.resolve_function_signature(&f.signature);
                this.with_scope(LexicalScopeSource::Plain, |this| this.visit_block(body))
            })
        } else {
            self.visit_generics(&f.generics);
            self.resolve_function_signature(&f.signature);
        }
    }

    fn visit_inheritance(&mut self, n: &taroc_hir::Inheritance) -> Self::Result {
        for interface_ref in &n.interfaces {
            self.resolve_path_with_source(
                interface_ref.id,
                &interface_ref.path,
                PathSource::Interface,
            );

            visitor::walk_tagged_path(self, interface_ref);
        }
    }
}

impl Actor<'_, '_> {
    fn resolve_declaration(
        &mut self,
        declaration: &taroc_hir::Declaration,
        context: taroc_hir::DeclarationContext,
    ) {
        let def_id = self.resolver.def_id(declaration.id);
        let def_kind = self.resolver.def_kind(def_id);

        match &declaration.kind {
            taroc_hir::DeclarationKind::Function(..) => {
                self.with_scope(LexicalScopeSource::Definition(def_kind), |this| {
                    this.with_generics_scope(def_id, |this| {
                        taroc_hir::visitor::walk_declaration(this, declaration, context);
                    });
                });
            }
            taroc_hir::DeclarationKind::Constructor(..) => {
                self.with_scope(LexicalScopeSource::Definition(def_kind), |this| {
                    this.with_generics_scope(def_id, |this| {
                        taroc_hir::visitor::walk_declaration(this, declaration, context);
                    })
                });
            }
            taroc_hir::DeclarationKind::Extend(extend) => {
                self.resolve_extend(extend, declaration, context);
            }
            taroc_hir::DeclarationKind::TypeAlias(..) => {
                self.with_scope(LexicalScopeSource::Definition(def_kind), |this| {
                    this.with_generics_scope(def_id, |this| {
                        taroc_hir::visitor::walk_declaration(this, declaration, context);
                    })
                });
            }
            taroc_hir::DeclarationKind::DefinedType(node) => {
                let def_context = self
                    .resolver
                    .get_context(&def_id)
                    .expect("must have context");
                let self_res = if matches!(node.kind, taroc_hir::DefinedTypeKind::Interface) {
                    Resolution::InterfaceSelfTypeAlias(def_id)
                } else {
                    Resolution::SelfTypeAlias(def_id)
                };
                self.with_scope(LexicalScopeSource::Context(def_context), |this| {
                    this.with_generics_scope(def_id, |this| {
                        this.with_self_alias_scope(self_res, |this| {
                            return taroc_hir::visitor::walk_declaration(
                                this,
                                declaration,
                                context,
                            );
                        });
                    });
                })
            }
            taroc_hir::DeclarationKind::Extern(_) => {
                taroc_hir::visitor::walk_declaration(self, declaration, context);
            }
            taroc_hir::DeclarationKind::Variable(_) | taroc_hir::DeclarationKind::Constant(..) => {
                taroc_hir::visitor::walk_declaration(self, declaration, context);
            }
            taroc_hir::DeclarationKind::Namespace(_) => {
                let def_context = self
                    .resolver
                    .get_context(&def_id)
                    .expect("namespace must have context");
                self.with_scope(LexicalScopeSource::Context(def_context), |this| {
                    taroc_hir::visitor::walk_declaration(this, declaration, context)
                })
            }
            taroc_hir::DeclarationKind::Bridge(_) => {}
            taroc_hir::DeclarationKind::Export(..) | taroc_hir::DeclarationKind::Import(..) => {
                taroc_hir::visitor::walk_declaration(self, declaration, context)
            }
            taroc_hir::DeclarationKind::Computed(_) => {
                taroc_hir::visitor::walk_declaration(self, declaration, context)
            }
            taroc_hir::DeclarationKind::AssociatedType(..) => {
                taroc_hir::visitor::walk_declaration(self, declaration, context)
            }
            taroc_hir::DeclarationKind::Operator(..) => {
                taroc_hir::visitor::walk_declaration(self, declaration, context)
            }
            taroc_hir::DeclarationKind::EnumCase(..) => {
                taroc_hir::visitor::walk_declaration(self, declaration, context)
            }
        }
    }
}

impl<'res, 'ctx> Actor<'res, 'ctx> {
    fn resolve_block(&mut self, block: &taroc_hir::Block) {
        let scope = if let Some(context) = self.resolver.get_block_context(&block.id) {
            LexicalScope::new(LexicalScopeSource::Context(context))
        } else {
            LexicalScope::new(LexicalScopeSource::Plain)
        };

        self.scopes.push(scope);
        taroc_hir::visitor::walk_block(self, block);
        self.scopes.pop();
    }
}

impl<'res, 'ctx> Actor<'res, 'ctx> {
    fn resolve_extend(
        &mut self,
        _: &taroc_hir::Extend,
        decl: &Declaration,
        ctx: DeclarationContext,
    ) {
        let extend_def_id = self.resolver.def_id(decl.id);
        let context = *self
            .resolver
            .resolved_extensions
            .get(&extend_def_id)
            .expect("resolved extension");

        let self_id = context.def_id().expect("context should map to definition");
        let self_res = Resolution::SelfTypeAlias(self_id);
        self.with_scope(LexicalScopeSource::Context(context), |this| {
            this.with_generics_scope(self_id, |this| {
                this.with_self_alias_scope(self_res, |this| {
                    taroc_hir::visitor::walk_declaration(this, &decl, ctx);
                });
            });
        });
    }
}

impl<'res, 'ctx> Actor<'res, 'ctx> {
    fn resolve_expression(&mut self, expr: &taroc_hir::Expression) {
        match &expr.kind {
            taroc_hir::ExpressionKind::Path(path) => {
                self.resolve_path_with_source(expr.id, path, PathSource::Expression);
                taroc_hir::visitor::walk_expression(self, expr);
            }
            _ => taroc_hir::visitor::walk_expression(self, expr),
        }
    }

    fn resolve_local(&mut self, local: &taroc_hir::Local) {
        if let Some(ty) = &local.ty {
            self.visit_type(ty);
        }

        if let Some(expr) = &local.initializer {
            self.visit_expression(expr)
        }

        self.resolve_top_level_binding_pattern(&local.pattern, PatternSource::Variable);
    }

    fn resolve_function_signature(&mut self, sg: &taroc_hir::FunctionSignature) {
        if let Some(ty) = &sg.prototype.output {
            self.visit_type(ty);
        }

        self.resolve_function_parameters(&sg.prototype.inputs);
    }
    fn resolve_function_parameters(&mut self, params: &Vec<taroc_hir::FunctionParameter>) {
        let mut seen = FxHashSet::default();
        for param in params.iter() {
            self.visit_type(&param.annotated_type);

            if let Some(e) = &param.default_value {
                self.visit_expression(e)
            }

            let pat = taroc_hir::BindingPattern {
                id: param.id,
                span: param.span,
                kind: taroc_hir::BindingPatternKind::Identifier(param.name.clone()),
            };

            self.resolve_binding_pattern(&pat, PatternSource::FunctionParameter, &mut seen);
        }
    }
}

impl<'res, 'ctx> Actor<'res, 'ctx> {
    fn resolve_top_level_binding_pattern(
        &mut self,
        pat: &taroc_hir::BindingPattern,
        source: PatternSource,
    ) {
        let mut bindings = FxHashSet::default();
        self.resolve_binding_pattern(pat, source, &mut bindings)
    }
    fn resolve_binding_pattern(
        &mut self,
        pat: &taroc_hir::BindingPattern,
        source: PatternSource,
        bindings: &mut FxHashSet<Symbol>,
    ) {
        match &pat.kind {
            taroc_hir::BindingPatternKind::Wildcard => {}
            taroc_hir::BindingPatternKind::Identifier(identifier) => {
                let res = self
                    .try_resolve_as_non_binding(source, &identifier)
                    .unwrap_or_else(|| {
                        self.fresh_var_from_binding_pattern(&identifier, pat.id, source, bindings)
                    });

                self.resolver.rescord_resolution(pat.id, res);
            }
            taroc_hir::BindingPatternKind::Tuple(binding_patterns) => {
                for pattern in binding_patterns {
                    self.resolve_binding_pattern(pattern, source, bindings);
                }
            }
        }
    }

    fn try_resolve_as_non_binding(
        &mut self,
        _source: PatternSource,
        _ident: &Identifier,
    ) -> Option<Resolution> {
        return None;
    }
    fn fresh_var_from_binding_pattern(
        &mut self,
        ident: &Identifier,
        id: NodeID,
        source: PatternSource,
        bindings: &mut FxHashSet<Symbol>,
    ) -> Resolution {
        let seen = bindings.contains(&ident.symbol);

        if seen {
            let err = match source {
                PatternSource::FunctionParameter => {
                    ResolutionError::IdentifierBoundMoreThanOnceInParameterList
                }
                _ => ResolutionError::IdentifierBoundMoreThanOnceInSamePattern,
            };

            self.report_error(err, ident.span);
        }

        let res = Resolution::Local(id);

        bindings.insert(ident.symbol.clone());

        let indx = self.scopes.len() - 1;
        self.scopes
            .get_mut(indx)
            .unwrap()
            .define(ident.symbol, res.clone());

        return res;
    }
}

impl<'res, 'ctx> Actor<'res, 'ctx> {
    fn resolve_path_with_source(
        &mut self,
        id: NodeID,
        path: &taroc_hir::Path,
        source: PathSource,
    ) -> Resolution {
        let segments = Segment::from_path(path);
        let result = self.resolve_path(&segments);

        let report_error = |this: &mut Self, res: Option<Resolution>| {
            this.report_error_with_context(path, source, res);
            return Resolution::Error;
        };
        let res = match result {
            Ok(Some(res)) => {
                if source.is_allowed(&res) || res.is_error() {
                    res
                } else {
                    report_error(self, Some(res))
                }
            }
            Err(err) => {
                self.report_error(err.value, err.span);
                Resolution::Error
            }

            _ => report_error(self, None),
        };

        self.resolver.rescord_resolution(id, res.clone());
        res
    }

    fn resolve_path(
        &mut self,
        path: &[Segment],
    ) -> Result<Option<Resolution>, Spanned<ResolutionError>> {
        match self.resolve_path_with_scopes(path) {
            PathResult::Context(context) => {
                return Ok(context.resolution());
            }
            PathResult::NonContext(res) => return Ok(Some(res)),
            PathResult::Indeterminate => {
                return Err(Spanned {
                    span: path.last().unwrap().identifier.span,
                    value: ResolutionError::Ambiguous {
                        segment: path.last().unwrap().identifier.symbol,
                    },
                });
            }
            PathResult::Failed {
                segment,
                is_last_segment: false,
            } => {
                return Err(Spanned {
                    span: segment.span,
                    value: ResolutionError::FailedToResolve {
                        segment: segment.symbol,
                    },
                });
            }
            PathResult::Failed { .. } => return Ok(None),
        };
    }

    fn resolve_path_with_scopes(&mut self, path: &[Segment]) -> PathResult<'ctx> {
        let res = self
            .resolver
            .resolve_path_with_scopes(path, &self.scopes, ResolutionState::Full);
        return res;
    }
}

impl<'res, 'ctx> Actor<'res, 'ctx> {
    fn report_error(&mut self, err: ResolutionError, span: Span) {
        let message = match err {
            ResolutionError::FailedToResolve { segment } => {
                format!("failed to resolve '{}'", segment)
            }
            ResolutionError::Ambiguous { segment } => {
                format!("ambiguous usage of glob '{}'", segment)
            }
            ResolutionError::IdentifierBoundMoreThanOnceInParameterList => {
                format!("identifier is bound more than once in the parameter list")
            }
            ResolutionError::IdentifierBoundMoreThanOnceInSamePattern => {
                format!("identifier is bound more than once in the pattern")
            }
            ResolutionError::CannotExtend { segment } => {
                format!("cannot extend {segment}")
            }
        };

        self.resolver.context.diagnostics.error(message, span);
    }

    fn report_error_with_context(
        &mut self,
        path: &taroc_hir::Path,
        source: PathSource,
        resolution: Option<Resolution>,
    ) {
        let item = path.segments.last().unwrap().identifier.symbol;
        let expectation = source.expected();

        if let Some(res) = resolution {
            let provided = res.description();
            let message = format!("expected {expectation}, got {provided} '{item}'");
            self.resolver.context.diagnostics.error(message, path.span);
            return;
        } else {
            let mod_name = if path.segments.len() == 1 {
                "scope"
            } else {
                path.segments[path.segments.len() - 2]
                    .identifier
                    .symbol
                    .as_str()
            };

            let message = format!("cannot find {expectation} '{item}' in {mod_name}");
            self.resolver.context.diagnostics.error(message, path.span);
        }
    }
}
