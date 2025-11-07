use std::ops::Add;

use ecow::EcoString;
use rustc_hash::FxHashMap;

use crate::{
    ast::{self, AstVisitor, Identifier, IdentifierPath, NodeID},
    error::CompileResult,
    sema::resolve::{
        DefinitionID, DefinitionKind, LexicalScope, LexicalScopeSource, Resolution, Scope, ScopeID,
        ScopeNamespace, resolver::Resolver,
    },
    span::Span,
};

pub fn resolve_package(package: &ast::Package, resolver: &mut Resolver) -> CompileResult<()> {
    let mut actor = Actor {
        resolver,
        scopes: vec![],
    };
    ast::walk_package(&mut actor, package);
    Ok(())
}

struct Actor<'resolver> {
    resolver: &'resolver mut Resolver,
    scopes: Vec<LexicalScope>,
}

impl<'r> Actor<'r> {
    fn with_scope<T>(&mut self, scope: LexicalScope, work: impl FnOnce(&mut Self) -> T) -> T {
        self.scopes.push(scope);
        let result = work(self);
        self.scopes.pop();
        result
    }

    fn with_scope_id<T>(&mut self, scope_id: ScopeID, work: impl FnOnce(&mut Self) -> T) -> T {
        self.with_scope(
            LexicalScope::new(LexicalScopeSource::Scoped(scope_id)),
            work,
        )
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
            let def_id = self.resolver.def_id(param.id);
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

        self.with_scope(scope, work);
    }

    fn with_self_alias_scope(&mut self, self_res: Resolution, work: impl FnOnce(&mut Self)) {
        let mut scope = LexicalScope::new(LexicalScopeSource::Plain);
        scope.define("Self".into(), self_res);
        self.with_scope(scope, work);
    }
}

impl<'r> ast::AstVisitor for Actor<'r> {
    fn visit_module(&mut self, node: &ast::Module, is_root: bool) -> Self::Result {
        // Soft Reset on Modular Level, So Module Root is Scope Count
        let previous = std::mem::take(&mut self.scopes);
        self.scopes = vec![];
        let module_id = 0;
        let scope_id = self.resolver.root_module_scope.unwrap();
        self.with_scope_id(scope_id, |this| ast::walk_module(this, node))
    }

    fn visit_file(&mut self, node: &ast::File) -> Self::Result {
        let scope_id = *self
            .resolver
            .file_scope_mapping
            .get(&node.id)
            .expect("unmapped file scope");
        self.with_scope_id(scope_id, |this| ast::walk_file(this, node))
    }

    fn visit_declaration(&mut self, node: &ast::Declaration) -> Self::Result {
        self.resolve_declaration(node);
    }

    fn visit_block(&mut self, node: &ast::Block) -> Self::Result {
        let scope = if let Some(&id) = self.resolver.block_scope_mapping.get(&node.id) {
            LexicalScope::new(LexicalScopeSource::Scoped(id))
        } else {
            LexicalScope::new(LexicalScopeSource::Plain)
        };
        self.with_scope(scope, |this| ast::walk_block(this, node))
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
                if let Some(arguments) = type_arguments {
                    ast::walk_type_arguments(self, arguments)
                }
                let parent = self.resolve_type_qualifier(parent);
                let carrier = self.apply_member(parent, name, Want::Final(ResolutionSource::Type));
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

impl<'r> Actor<'r> {
    fn resolve_declaration(&mut self, declaration: &ast::Declaration) {
        match &declaration.kind {
            ast::DeclarationKind::TypeAlias(ast::TypeAlias { generics, .. })
            | ast::DeclarationKind::Function(ast::Function { generics, .. }) => {
                let def_id = self.resolver.def_id(declaration.id);
                self.with_scope(
                    LexicalScope::new(LexicalScopeSource::Definition(def_id)),
                    |this| {
                        this.with_generics_scope(generics, |this| {
                            ast::walk_declaration(this, declaration)
                        });
                    },
                )
            }
            ast::DeclarationKind::Interface(node) => {
                let def_id = self.resolver.def_id(declaration.id);
                let self_res = Resolution::InterfaceSelfTypeParameter(def_id);
                self.with_scope(
                    LexicalScope::new(LexicalScopeSource::Definition(def_id)),
                    |this| {
                        this.with_generics_scope(&node.generics, |this| {
                            this.with_self_alias_scope(self_res, |this| {
                                ast::walk_declaration(this, declaration)
                            });
                        });
                    },
                )
            }
            ast::DeclarationKind::Enum(ast::Enum { generics, .. })
            | ast::DeclarationKind::Struct(ast::Struct { generics, .. }) => {
                let def_id = self.resolver.def_id(declaration.id);
                let self_res = Resolution::SelfTypeAlias(def_id);
                self.with_scope(
                    LexicalScope::new(LexicalScopeSource::Definition(def_id)),
                    |this| {
                        this.with_generics_scope(generics, |this| {
                            this.with_self_alias_scope(self_res, |this| {
                                ast::walk_declaration(this, declaration)
                            });
                        });
                    },
                )
            }
            ast::DeclarationKind::Variable(..)
            | ast::DeclarationKind::Constant(..)
            | ast::DeclarationKind::Import(..)
            | ast::DeclarationKind::Export(..) => ast::walk_declaration(self, declaration),
            ast::DeclarationKind::Namespace(namespace) => {
                let def_id = self.resolver.def_id(declaration.id);
                let scope_id = self.resolver.get_def_scope(def_id);
                self.with_scope_id(scope_id, |this| ast::walk_declaration(this, declaration))
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

impl<'r> Actor<'r> {
    fn resolve_extension(&mut self, id: ast::NodeID, node: &ast::Implementation) {
        let def_id = self.resolver.def_id(id);
        self.with_scope(
            LexicalScope::new(LexicalScopeSource::Definition(def_id)),
            |this| {
                this.with_generics_scope(&node.generics, |this| {
                    let self_res = Resolution::SelfTypeAlias(def_id);
                    this.with_self_alias_scope(self_res, |this| {
                        this.visit_type(&node.ty);
                        this.visit_generics(&node.generics);

                        for declaration in &node.declarations {
                            this.resolve_extension_declaration(declaration);
                        }
                    });
                });
            },
        )
    }

    fn resolve_extension_declaration(&mut self, declaration: &ast::AssociatedDeclaration) {
        println!("Extension decl")
    }
}

impl<'r> Actor<'r> {
    fn get_resolution(&mut self, node: NodeID) -> Option<Resolution> {
        None
    }
}
impl<'r> Actor<'r> {
    fn resolve_interface(&mut self, node: &ast::Type) {}
}

impl<'r> Actor<'r> {
    fn resolve_identifier(&mut self, id: NodeID, name: &Identifier, source: ResolutionSource) {
        let result = self
            .resolver
            .resolve_in_scopes(name, source.namespace(), &self.scopes);
    }

    fn resolve_identifier_internal(
        &mut self,
        name: &Identifier,
        namespace: ScopeNamespace,
    ) -> Result<ResolutionResult, ()> {
        let result = self
            .resolver
            .resolve_in_scopes(name, namespace, &self.scopes);
        Err(())
    }

    fn resolve_type_qualifier(&mut self, node: &ast::Type) -> Carrier {
        match &node.kind {
            ast::TypeKind::Nominal { name, .. } => {
                {
                    let module_result =
                        self.resolve_identifier_internal(name, ScopeNamespace::Module);
                    if let Ok(ResolutionResult::Module(module)) = module_result {
                        return Carrier::Module(module);
                    }
                }

                {
                    let type_result = self.resolve_identifier_internal(name, ScopeNamespace::Type);
                    if let Ok(ResolutionResult::Res(res)) = type_result {
                        todo!()
                    }
                }

                println!("Cannot Find Top Level {}", name.symbol);
                return Carrier::Error;
            }
            ast::TypeKind::Member {
                parent: target,
                name,
                ..
            } => {
                let lhs = self.resolve_type_qualifier(target);
                self.apply_member(lhs, name, Want::Qualifier)
            }
            _ => {
                todo!()
            }
        }
    }

    fn apply_member(&mut self, lhs: Carrier, name: &Identifier, want: Want) -> Carrier {
        match lhs {
            Carrier::Module(_) => todo!(),
            Carrier::NominalType(definition_id) => todo!(),
            Carrier::Error => Carrier::Error,
        }
    }
}

enum Carrier {
    Module(ModuleOrNamespace),
    NominalType(DefinitionID),
    Error,
}

enum Want {
    Qualifier,
    Final(ResolutionSource),
}

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

pub enum ResolutionResult {
    Module(ModuleOrNamespace),
    Res(Resolution),
    Error,
}

pub enum ModuleOrNamespace {
    Module(usize),
    Namespace(DefinitionID),
}
