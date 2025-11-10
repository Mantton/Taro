use crate::{
    ast::{self, AstVisitor, Identifier, IdentifierPath, NodeID, Path},
    diagnostics::{Diagnostic, DiagnosticLevel},
    error::CompileResult,
    sema::resolve::{
        models::{
            DefinitionID, DefinitionKind, LexicalScope, LexicalScopeBinding, LexicalScopeSource,
            PathResult, Resolution, ResolutionError, ResolutionSource, ResolutionState,
            ResolvedValue, Scope, ScopeNamespace,
        },
        resolver::Resolver,
    },
    span::Span,
};
use ecow::EcoString;
use rustc_hash::FxHashMap;
use std::{mem, ops::Add};

pub fn resolve_package(package: &ast::Package, resolver: &mut Resolver) -> CompileResult<()> {
    let mut actor = Actor {
        resolver,
        scopes: vec![],
    };
    ast::walk_package(&mut actor, package);
    resolver.compiler.dcx.ok()
}

struct Actor<'r, 'a, 'c> {
    resolver: &'r mut Resolver<'a, 'c>,
    scopes: Vec<LexicalScope<'a>>,
}

impl<'r, 'a, 'c> Actor<'r, 'a, 'c> {
    fn with_scope_source<T>(
        &mut self,
        source: LexicalScopeSource<'a>,
        work: impl FnOnce(&mut Self) -> T,
    ) -> T {
        self.scopes.push(LexicalScope::new(source));
        let result = work(self);
        self.scopes.pop();
        result
    }

    fn with_built_scope<T>(
        &mut self,
        scope: LexicalScope<'a>,
        work: impl FnOnce(&mut Self) -> T,
    ) -> T {
        self.scopes.push(scope);
        let result = work(self);
        self.scopes.pop();
        result
    }

    fn with_scope<T>(&mut self, scope: Scope<'a>, work: impl FnOnce(&mut Self) -> T) -> T {
        self.scopes
            .push(LexicalScope::new(LexicalScopeSource::Scoped(scope)));
        let result = work(self);
        self.scopes.pop();
        result
    }

    fn with_generics_scope(&mut self, generics: &ast::Generics, work: impl FnOnce(&mut Self)) {
        let type_parameters = &generics.type_parameters;
        let Some(type_parameters) = type_parameters else {
            work(self);
            return;
        };

        let mut seen_bindings: FxHashMap<EcoString, Span> = Default::default();

        let mut scope = LexicalScope::new(LexicalScopeSource::Plain);
        for param in &type_parameters.parameters {
            let def_id = self.resolver.definition_id(param.id);
            let name = param.identifier.symbol.clone();
            let entry = seen_bindings.entry(name.clone());

            match entry {
                std::collections::hash_map::Entry::Occupied(_) => {
                    // param has already been defined
                    self.resolver.dcx().emit_error(
                        format!(
                            "type parameter – {} – has already been defined",
                            param.identifier.symbol
                        ),
                        param.identifier.span,
                    );
                    continue;
                }
                std::collections::hash_map::Entry::Vacant(entry) => {
                    // mark as seen
                    entry.insert(param.identifier.span);
                }
            }

            //     self.resolver.record_resolution(
            //         param.id,
            //         PartialResolution::new(Resolution::Definition(
            //             def_id,
            //             DefinitionKind::TypeParameter,
            //         )),
            //     );
            scope.define(
                name,
                Resolution::Definition(def_id, DefinitionKind::TypeParameter),
            );
        }

        self.with_built_scope(scope, work);
    }

    fn with_self_alias_scope(&mut self, self_res: Resolution, work: impl FnOnce(&mut Self)) {
        let mut scope = LexicalScope::new(LexicalScopeSource::Plain);
        scope.define("Self".into(), self_res);
        self.with_built_scope(scope, work);
    }
}

impl<'r, 'a, 'c> ast::AstVisitor for Actor<'r, 'a, 'c> {
    fn visit_module(&mut self, node: &ast::Module, is_root: bool) -> Self::Result {
        // Soft Reset on Modular Level, So Module Root is Scope Count
        let previous = std::mem::take(&mut self.scopes);
        self.scopes = vec![];
        let module_id = 0;
        let scope = self.resolver.root_module_scope.unwrap();
        self.with_scope(scope, |this| ast::walk_module(this, node))
    }

    fn visit_file(&mut self, node: &ast::File) -> Self::Result {
        let scope = *self
            .resolver
            .file_scope_mapping
            .get(&node.id)
            .expect("unmapped file scope");
        self.with_scope(scope, |this| ast::walk_file(this, node))
    }

    fn visit_declaration(&mut self, node: &ast::Declaration) -> Self::Result {
        self.resolve_declaration(node);
    }

    fn visit_block(&mut self, node: &ast::Block) -> Self::Result {
        let scope = if let Some(&scope) = self.resolver.block_scope_mapping.get(&node.id) {
            LexicalScopeSource::Scoped(scope)
        } else {
            LexicalScopeSource::Plain
        };
        self.with_scope_source(scope, |this| ast::walk_block(this, node))
    }

    fn visit_type(&mut self, node: &ast::Type) -> Self::Result {
        match &node.kind {
            ast::TypeKind::Nominal(path) => {
                self.resolve_path_with_source(node.id, path, ResolutionSource::Type);
            }
            ast::TypeKind::QualifiedMember {
                self_ty,
                interface,
                member,
            } => {
                // TODO
            }
            ast::TypeKind::BoxedExistential { interfaces } => {
                for path in interfaces {
                    self.resolve_path_with_source(node.id, path, ResolutionSource::Interface);
                }
            }
            _ => {}
        }
        ast::walk_type(self, node)
    }
}

impl<'r, 'a, 'c> Actor<'r, 'a, 'c> {
    fn resolve_declaration(&mut self, declaration: &ast::Declaration) {
        match &declaration.kind {
            ast::DeclarationKind::TypeAlias(ast::TypeAlias { generics, .. })
            | ast::DeclarationKind::Function(ast::Function { generics, .. }) => {
                let def_id = self.resolver.definition_id(declaration.id);
                self.with_scope_source(LexicalScopeSource::DefBoundary(def_id), |this| {
                    this.with_generics_scope(generics, |this| {
                        ast::walk_declaration(this, declaration)
                    });
                })
            }
            ast::DeclarationKind::Interface(node) => {
                let def_id = self.resolver.definition_id(declaration.id);
                let self_res = Resolution::InterfaceSelfTypeParameter(def_id);
                self.with_scope_source(LexicalScopeSource::DefBoundary(def_id), |this| {
                    this.with_generics_scope(&node.generics, |this| {
                        this.with_self_alias_scope(self_res, |this| {
                            ast::walk_declaration(this, declaration)
                        });
                    });
                })
            }
            ast::DeclarationKind::Enum(ast::Enum { generics, .. })
            | ast::DeclarationKind::Struct(ast::Struct { generics, .. }) => {
                let def_id = self.resolver.definition_id(declaration.id);
                let self_res = Resolution::SelfTypeAlias(def_id);
                self.with_scope_source(LexicalScopeSource::DefBoundary(def_id), |this| {
                    this.with_generics_scope(generics, |this| {
                        this.with_self_alias_scope(self_res, |this| {
                            ast::walk_declaration(this, declaration)
                        });
                    });
                })
            }
            ast::DeclarationKind::Variable(..)
            | ast::DeclarationKind::Constant(..)
            | ast::DeclarationKind::Import(..)
            | ast::DeclarationKind::Export(..) => ast::walk_declaration(self, declaration),
            ast::DeclarationKind::Namespace(namespace) => {
                let def_id = self.resolver.definition_id(declaration.id);
                let scope = self.resolver.get_definition_scope(def_id);
                self.with_scope(scope, |this| ast::walk_declaration(this, declaration))
            }
            ast::DeclarationKind::Implementation(node) => {
                self.resolve_extension(declaration.id, node)
            }
            ast::DeclarationKind::Initializer(..) => {
                unreachable!("top level initializer")
            }
        }
    }
}

impl<'r, 'a, 'c> Actor<'r, 'a, 'c> {
    fn resolve_extension(&mut self, id: ast::NodeID, node: &ast::Implementation) {
        let def_id = self.resolver.definition_id(id);
        self.with_scope_source(LexicalScopeSource::DefBoundary(def_id), |this| {
            this.with_generics_scope(&node.generics, |this| {
                let self_res = Resolution::SelfTypeAlias(def_id);
                this.with_self_alias_scope(self_res, |this| {
                    this.visit_type(&node.ty);
                    this.visit_generics(&node.generics);

                    for declaration in &node.declarations {
                        this.resolve_impl_declaration(declaration);
                    }
                });
            });
        })
    }

    fn resolve_impl_declaration(&mut self, declaration: &ast::AssociatedDeclaration) {
        println!("Extension decl")
    }
}

impl<'r, 'a, 'c> Actor<'r, 'a, 'c> {
    fn resolve_identifier_with_source(
        &mut self,
        id: NodeID,
        name: &Identifier,
        source: ResolutionSource,
    ) {
    }

    fn resolve_path_with_source(&mut self, id: NodeID, path: &Path, source: ResolutionSource) {
        let result =
            self.resolver
                .resolve_path_in_scopes(&path.segments, source.namespace(), &self.scopes);

        println!("Success {}", !matches!(result, PathResult::Failed { .. }));
        let result = match result {
            PathResult::Scope(scope) => Some(scope.resolution().unwrap()),
            PathResult::Resolution(value) => match value {
                ResolutionState::Complete(resolution) => Some(resolution),
                ResolutionState::Partial { .. } => None,
            },
            PathResult::Failed {
                segment,
                is_last_segment,
                error,
            } => {
                let diag = self.diag(&segment, error);
                self.resolver.dcx().emit(diag);
                return;
            }
        };

        if let Some(result) = result {
            if !source.is_allowed(&result) {
                println!("Unallowed resolution in position")
            }
        } else if !source.defer_to_type_checker() {
            println!("Unallowd reoslution in position")
        }
    }
}

impl<'r, 'a, 'c> Actor<'r, 'a, 'c> {
    fn diag(&self, identifier: &Identifier, err: ResolutionError) -> Diagnostic {
        let name = &identifier.symbol;
        let span = identifier.span;
        let msg = match err {
            ResolutionError::NotAModule => format!("'{}' is not a module", name),
            ResolutionError::NotAType => format!("'{}' is not a module", name),
            ResolutionError::NotAnInterface => format!("'{}' is not an interface", name),
            ResolutionError::UnknownSymbol => format!("cannot resolve symbol '{}' in scope", name),
            ResolutionError::AlreadyInScope(span) => {
                format!("'{}' is already defined in scope", name)
            }
            ResolutionError::AmbiguousUsage => {
                format!("ambiguous use of '{}'", name)
            }
        };

        Diagnostic::new(msg, span, DiagnosticLevel::Error)
    }
}
