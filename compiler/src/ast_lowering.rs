use crate::{
    ast::{self, AssocContext},
    compile::state::CompilerState,
    error::{CompileResult, ReportedError},
    hir,
};

pub fn lower_package(package: ast::Package, state: CompilerState) -> CompileResult<hir::Package> {
    let mut actor = Actor::new(state);
    let root = actor.lower_module(package.root);
    state.dcx.ok()?;
    Ok(hir::Package { root })
}

pub struct Actor<'ctx> {
    pub context: CompilerState<'ctx>,
    pub next_index: u32,
}

impl Actor<'_> {
    fn new<'a>(context: CompilerState<'a>) -> Actor<'a> {
        Actor {
            context,
            next_index: 0,
        }
    }

    fn next_index(&mut self) -> hir::NodeID {
        let index = hir::NodeID::from_raw(self.next_index);
        self.next_index += 1;
        index
    }
}

impl Actor<'_> {
    fn lower_module(&mut self, module: ast::Module) -> hir::Module {
        let declarations: Vec<hir::Declaration> = module
            .files
            .into_iter()
            .flat_map(|file| self.lower_file(file))
            .collect();

        let submodules: Vec<hir::Module> = module
            .submodules
            .into_iter()
            .map(|file| self.lower_module(file))
            .collect();

        hir::Module {
            id: self.next_index(),
            name: module.name,
            declarations,
            submodules,
        }
    }

    fn lower_file(&mut self, file: ast::File) -> Vec<hir::Declaration> {
        file.declarations
            .into_iter()
            .map(|node| self.lower_declaration(node))
            .collect()
    }
}

impl Actor<'_> {
    fn lower_declaration(&mut self, node: ast::Declaration) -> hir::Declaration {
        let kind = match node.kind {
            ast::DeclarationKind::Interface(node) => {
                hir::DeclarationKind::Interface(self.lower_interface(node))
            }
            ast::DeclarationKind::Struct(node) => {
                hir::DeclarationKind::Struct(self.lower_struct(node))
            }
            ast::DeclarationKind::Enum(node) => hir::DeclarationKind::Enum(self.lower_enum(node)),
            ast::DeclarationKind::TypeAlias(node) => {
                hir::DeclarationKind::TypeAlias(self.lower_alias(node))
            }
            ast::DeclarationKind::Function(node) => {
                hir::DeclarationKind::Function(self.lower_function(node))
            }
            ast::DeclarationKind::Constant(node) => {
                hir::DeclarationKind::Constant(self.lower_constant(node))
            }
            ast::DeclarationKind::Import(node) => {
                hir::DeclarationKind::Import(self.lower_use_tree(node))
            }
            ast::DeclarationKind::Export(node) => {
                hir::DeclarationKind::Export(self.lower_use_tree(node))
            }
            ast::DeclarationKind::Namespace(node) => {
                hir::DeclarationKind::Namespace(self.lower_namespace(node))
            }
            ast::DeclarationKind::Variable(local) => todo!(),
            ast::DeclarationKind::Extension(node) => {
                hir::DeclarationKind::Extension(self.lower_extension(node))
            }
            ast::DeclarationKind::Initializer(..) | ast::DeclarationKind::Operator(..) => {
                unreachable!()
            }
        };

        hir::Declaration {
            id: self.next_index(),
            span: node.span,
            kind,
            attributes: vec![],
        }
    }

    fn lower_function_declaration(&mut self, node: ast::FunctionDeclaration) -> hir::Declaration {
        let kind = match node.kind {
            ast::FunctionDeclarationKind::Struct(node) => {
                hir::DeclarationKind::Struct(self.lower_struct(node))
            }
            ast::FunctionDeclarationKind::Enum(node) => {
                hir::DeclarationKind::Enum(self.lower_enum(node))
            }
            ast::FunctionDeclarationKind::TypeAlias(node) => {
                hir::DeclarationKind::TypeAlias(self.lower_alias(node))
            }
            ast::FunctionDeclarationKind::Import(node) => {
                hir::DeclarationKind::Import(self.lower_use_tree(node))
            }
            ast::FunctionDeclarationKind::Function(node) => {
                hir::DeclarationKind::Function(self.lower_function(node))
            }
            ast::FunctionDeclarationKind::Constant(node) => {
                hir::DeclarationKind::Constant(self.lower_constant(node))
            }
        };

        hir::Declaration {
            id: self.next_index(),
            span: node.span,
            kind,
            attributes: vec![],
        }
    }

    fn lower_namespace_declaration(&mut self, node: ast::NamespaceDeclaration) -> hir::Declaration {
        let kind = match node.kind {
            ast::NamespaceDeclarationKind::Struct(node) => {
                hir::DeclarationKind::Struct(self.lower_struct(node))
            }
            ast::NamespaceDeclarationKind::Enum(node) => {
                hir::DeclarationKind::Enum(self.lower_enum(node))
            }
            ast::NamespaceDeclarationKind::Interface(node) => {
                hir::DeclarationKind::Interface(self.lower_interface(node))
            }
            ast::NamespaceDeclarationKind::TypeAlias(node) => {
                hir::DeclarationKind::TypeAlias(self.lower_alias(node))
            }
            ast::NamespaceDeclarationKind::Import(node) => {
                hir::DeclarationKind::Import(self.lower_use_tree(node))
            }
            ast::NamespaceDeclarationKind::Export(node) => {
                hir::DeclarationKind::Export(self.lower_use_tree(node))
            }
            ast::NamespaceDeclarationKind::Function(node) => {
                hir::DeclarationKind::Function(self.lower_function(node))
            }
            ast::NamespaceDeclarationKind::Constant(node) => {
                hir::DeclarationKind::Constant(self.lower_constant(node))
            }
            ast::NamespaceDeclarationKind::Namespace(node) => {
                hir::DeclarationKind::Namespace(self.lower_namespace(node))
            }
        };

        hir::Declaration {
            id: self.next_index(),
            span: node.span,
            kind,
            attributes: vec![],
        }
    }

    fn lower_assoc_declaration(
        &mut self,
        node: ast::AssociatedDeclaration,
        ctx: AssocContext,
    ) -> hir::AssociatedDeclaration {
        let kind = match node.kind {
            ast::AssociatedDeclarationKind::Constant(node) => {
                hir::AssociatedDeclarationKind::Constant(self.lower_constant(node))
            }
            ast::AssociatedDeclarationKind::Function(node) => {
                hir::AssociatedDeclarationKind::Function(self.lower_function(node))
            }
            ast::AssociatedDeclarationKind::AssociatedType(node) => {
                hir::AssociatedDeclarationKind::Type(self.lower_alias(node))
            }
            ast::AssociatedDeclarationKind::Initializer(node) => {
                hir::AssociatedDeclarationKind::Initializer(self.lower_initializer(node))
            }
            ast::AssociatedDeclarationKind::Operator(node) => {
                hir::AssociatedDeclarationKind::Operator(self.lower_operator(node))
            }
        };

        hir::AssociatedDeclaration {
            id: self.next_index(),
            span: node.span,
            kind,
            attributes: vec![],
        }
    }
}

impl Actor<'_> {
    fn lower_interface(&mut self, node: ast::Interface) -> hir::Interface {
        todo!()
    }

    fn lower_struct(&mut self, node: ast::Struct) -> hir::Struct {
        todo!()
    }

    fn lower_enum(&mut self, node: ast::Enum) -> hir::Enum {
        todo!()
    }

    fn lower_alias(&mut self, node: ast::TypeAlias) -> hir::TypeAlias {
        todo!()
    }

    fn lower_constant(&mut self, node: ast::Constant) -> hir::Constant {
        todo!()
    }

    fn lower_use_tree(&mut self, node: ast::UseTree) -> hir::UseTree {
        todo!()
    }
}

impl Actor<'_> {
    fn lower_operator(&mut self, node: ast::Operator) -> hir::Operator {
        todo!()
    }

    fn lower_initializer(&mut self, node: ast::Initializer) -> hir::Initializer {
        todo!()
    }

    fn lower_function(&mut self, node: ast::Function) -> hir::Function {
        todo!()
    }
}

impl Actor<'_> {
    fn lower_extension(&mut self, node: ast::Extension) -> hir::Extension {
        todo!()
    }
    fn lower_namespace(&mut self, node: ast::Namespace) -> hir::Namespace {
        todo!()
    }
}
