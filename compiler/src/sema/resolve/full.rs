use crate::{
    ast::{self, AstVisitor, Identifier, IdentifierPath, NodeID},
    error::CompileResult,
    sema::resolve::{
        models::{
            DefinitionID, DefinitionKind, LexicalScope, LexicalScopeBinding, LexicalScopeSource,
            Resolution, ResolutionError, ResolvedValue, Scope, ScopeNamespace,
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
    Ok(())
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
                    todo!("report error – param has already been defined");
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
            ast::TypeKind::Nominal {
                name,
                type_arguments,
            } => {
                self.resolve_identifier(node.id, name, ResolutionSource::Type);
                ast::walk_type(self, node)
            }
            ast::TypeKind::Member {
                parent,
                name,
                type_arguments,
            } => {
                let parent = self.resolve_type_qualifier(parent);
                let carrier = self.apply_member(parent, name, Want::Final(ResolutionSource::Type));
                if let Some(arguments) = type_arguments {
                    ast::walk_type_arguments(self, arguments)
                }
                match carrier {
                    Carrier::Module(interned) => println!("{} – Module", name.symbol),
                    Carrier::NominalType(definition_id) => println!("{} – Definition", name.symbol),
                    Carrier::Error => println!("{} – Error", name.symbol),
                }
            }
            ast::TypeKind::QualifiedMember {
                self_ty,
                interface,
                name,
                type_arguments,
            } => {
                self.visit_type(self_ty);
                self.resolve_interface(interface);
                // TODO: This might need a "Do-Later" Tag
                if let Some(arguments) = type_arguments {
                    ast::walk_type_arguments(self, arguments)
                }
            }
            ast::TypeKind::BoxedExistential { interfaces } => {
                for interface in interfaces {
                    self.resolve_interface(interface);
                }
            }
            _ => ast::walk_type(self, node),
        }
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
    fn resolve_interface(&mut self, node: &ast::Type) {
        match &node.kind {
            ast::TypeKind::Nominal {
                name,
                type_arguments,
            } => {
                let result = self.resolve_identifier_internal(name, ScopeNamespace::Type);
                match result {
                    Ok(value) => {
                        let resolution = value.resolution();
                        let Resolution::Definition(_, DefinitionKind::Interface) = resolution
                        else {
                            todo!("report – not an interface")
                        };
                    }
                    Err(_) => todo!(),
                }
                if let Some(arguments) = type_arguments {
                    ast::walk_type_arguments(self, arguments)
                }
            }
            ast::TypeKind::Member {
                parent,
                name,
                type_arguments,
            } => {
                let parent = self.resolve_type_qualifier(parent);
                let carrier =
                    self.apply_member(parent, name, Want::Final(ResolutionSource::Interface));

                debug_assert!(!matches!(carrier, Carrier::Error));
                if let Some(arguments) = type_arguments {
                    ast::walk_type_arguments(self, arguments)
                }
            }
            ast::TypeKind::Parenthesis(node) => {
                return self.resolve_interface(node);
            }
            _ => {
                todo!("report invalid interface")
            }
        }
    }
}

impl<'r, 'a, 'c> Actor<'r, 'a, 'c> {
    fn resolve_identifier(&mut self, id: NodeID, name: &Identifier, source: ResolutionSource) {
        let result = self.resolve_identifier_internal(name, source.namespace());

        match result {
            Ok(value) => {
                let resolution = value.resolution();
                println!("{} – Definition", name.symbol)
            }
            Err(_) => todo!(),
        }
    }

    fn resolve_identifier_internal(
        &mut self,
        name: &Identifier,
        namespace: ScopeNamespace,
    ) -> Result<ResolvedValue<'a>, ResolutionError> {
        let result = self
            .resolver
            .resolve_in_scopes(name, namespace, &self.scopes);

        match result {
            Some(value) => Ok(value),
            None => todo!(),
        }
    }

    fn resolve_type_qualifier(&mut self, node: &ast::Type) -> Carrier<'a> {
        match &node.kind {
            ast::TypeKind::Nominal { name, .. } => {
                {
                    let module_result =
                        self.resolve_identifier_internal(name, ScopeNamespace::Module);
                    if let Ok(ResolvedValue::Scope(module)) = module_result {
                        return Carrier::Module(module);
                    }
                }

                {
                    let type_result = self.resolve_identifier_internal(name, ScopeNamespace::Type);
                    if let Ok(ResolvedValue::Resolution(Resolution::Definition(id, _))) =
                        type_result
                    {
                        return Carrier::NominalType(id);
                    }
                }

                println!("Cannot Find Top Level {}", name.symbol);
                return Carrier::Error;
            }
            ast::TypeKind::Member { parent, name, .. } => {
                let lhs = self.resolve_type_qualifier(parent);
                let carrier = self.apply_member(lhs, name, Want::Qualifier);
                return carrier;
            }
            _ => {
                todo!()
            }
        }
    }

    fn apply_member(&mut self, lhs: Carrier<'a>, name: &Identifier, want: Want) -> Carrier<'a> {
        match lhs {
            Carrier::Module(scope) => {
                for &ns in &[ScopeNamespace::Module, ScopeNamespace::Type] {
                    let member = self.resolver.resolve_in_scope(name, scope, ns);
                    if let Ok(member) = member {
                        let carrier: Carrier<'_> = match &want {
                            Want::Qualifier => match member {
                                ResolvedValue::Scope(scope) => Carrier::Module(scope),
                                ResolvedValue::Resolution(Resolution::Definition(id, _)) => {
                                    Carrier::NominalType(id)
                                }
                                _ => todo!(),
                            },
                            Want::Final(source) => {
                                let resolution = member.resolution();
                                match (source, resolution) {
                                    (
                                        ResolutionSource::Type,
                                        Resolution::Definition(
                                            id,
                                            DefinitionKind::TypeAlias
                                            | DefinitionKind::Enum
                                            | DefinitionKind::Struct,
                                        ),
                                    ) => Carrier::NominalType(id),
                                    (
                                        ResolutionSource::Interface,
                                        Resolution::Definition(id, DefinitionKind::Interface),
                                    ) => Carrier::NominalType(id),
                                    _ => todo!(),
                                }
                            }
                        };
                        return carrier;
                    }
                }

                // No Resolution
                Carrier::Error
            }
            Carrier::NominalType(definition_id) => todo!(),
            Carrier::Error => Carrier::Error,
        }
    }
}

#[derive(Debug)]
enum Carrier<'a> {
    Module(Scope<'a>),
    NominalType(DefinitionID),
    Error,
}

enum Want {
    Qualifier,
    Final(ResolutionSource),
}

#[derive(Debug)]
pub enum ResolutionSource {
    Type,
    Interface,
}

impl ResolutionSource {
    pub fn namespace(&self) -> ScopeNamespace {
        match self {
            ResolutionSource::Type | ResolutionSource::Interface => ScopeNamespace::Type,
        }
    }
}
