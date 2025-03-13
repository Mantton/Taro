use std::collections::HashMap;
use taroc_ast::{
    BindingPatternKind, Bridge, BridgeValue, ComputedVariable, Conform, Declaration,
    DeclarationContext, DeclarationKind, Enum, Extend, Extern, Interface, Local, ModuleKind,
    Mutability, Namespace, PathTree, PathTreeNode, Struct, TypeAlias, VariantKind,
};
use taroc_span::{Identifier, SpannedMessage, Symbol};
use taroc_token::{Delimiter, TokenKind};

use super::package::{Parser, R};

impl Parser {
    pub fn parse_declaration(
        &mut self,
        force: bool,
        context: DeclarationContext,
    ) -> R<Option<Declaration>> {
        self.consume_comments_and_new_lines();
        let start_span = self.lo_span();
        let attributes = self.parse_attributes()?;
        let visibility = self.parse_visibility()?;

        let Some((identifier, kind)) = self.parse_decl_kind(context)? else {
            if force {
                let msg = format!(
                    "expected declaration, found '{}' instead",
                    self.current_kind()
                );
                return Err(SpannedMessage::new(msg, self.current_token_span()));
            }
            return Ok(None);
        };

        let decl = Declaration {
            span: start_span.to(self.hi_span()),
            identifier,
            kind,
            visibility,
            attributes,
        };

        Ok(Some(decl))
    }
}

impl Parser {
    fn parse_decl_kind(
        &mut self,
        context: DeclarationContext,
    ) -> R<Option<(Identifier, DeclarationKind)>> {
        let current_kind = self.current_kind();
        let (identifier, kind) = match current_kind {
            TokenKind::Let => self.parse_top_level_variable_decl()?,
            TokenKind::Var => {
                if matches!(
                    context,
                    DeclarationContext::Extend
                        | DeclarationContext::Conform
                        | DeclarationContext::Interface
                ) {
                    self.parse_computed_variable()?
                } else {
                    self.parse_top_level_variable_decl()?
                }
            }
            TokenKind::Import => (
                Identifier::emtpy(self.file.file),
                self.parse_use_declaration(true)?,
            ),
            TokenKind::Export => (
                Identifier::emtpy(self.file.file),
                self.parse_use_declaration(false)?,
            ),
            TokenKind::Mod => self.parse_mod_declaration()?,
            TokenKind::Type => self.parse_type_declaration()?,
            TokenKind::Struct => self.parse_struct_declaration()?,
            TokenKind::Enum => self.parse_enum_declaration()?,
            TokenKind::Function => self.parse_function()?,
            TokenKind::Init => (Identifier::emtpy(self.file.file), self.parse_constructor()?),
            TokenKind::Interface => self.parse_interface()?,
            TokenKind::Extern => (Identifier::emtpy(self.file.file), self.parse_extern()?),
            TokenKind::Conform => (Identifier::emtpy(self.file.file), self.parse_conform()?),
            TokenKind::Extend => (Identifier::emtpy(self.file.file), self.parse_extend()?),
            TokenKind::Bridge => self.parse_bridge()?,
            TokenKind::Namespace => self.parse_namespace()?,
            _ => return Ok(None),
        };

        Ok(Some((identifier, kind)))
    }
}

impl Parser {
    fn parse_top_level_variable_decl(&mut self) -> R<(Identifier, DeclarationKind)> {
        let mutability = if self.eat(TokenKind::Let) {
            Mutability::Immutable
        } else if self.eat(TokenKind::Var) {
            Mutability::Mutable
        } else {
            unreachable!()
        };

        let pattern = self.parse_binding_pat()?;
        let ident = match pattern.kind {
            BindingPatternKind::Identifier(identifier) => identifier,
            _ => {
                self.result.error(SpannedMessage::new(
                    "Top Level Variables and Constants MUST use Identifier Binding Pattern Only"
                        .into(),
                    pattern.span,
                ));
                Identifier::emtpy(self.file.file)
            }
        };
        let ty = if self.eat(TokenKind::Colon) {
            Some(self.parse_type()?)
        } else {
            None
        };

        let initializer = if self.eat(TokenKind::Assign) {
            Some(self.parse_expression()?)
        } else {
            None
        };

        let local = Local {
            mutability,
            pattern,
            ty,
            initializer,
            is_shorthand: false,
        };

        self.expect(TokenKind::Semicolon)?;
        Ok((ident, DeclarationKind::Variable(local)))
    }
}

impl Parser {
    fn parse_type_declaration(&mut self) -> R<(Identifier, DeclarationKind)> {
        self.expect(TokenKind::Type)?;
        let identifier = self.parse_identifier()?;
        let mut generics = self.parse_generics()?;

        let ty = if self.eat(TokenKind::Assign) {
            Some(self.parse_type()?)
        } else {
            None
        };

        generics.where_clause = self.parse_generic_where_clause()?;

        let decl = TypeAlias { generics, ty };

        let k = DeclarationKind::TypeAlias(decl);
        self.expect_line_break_or_semi()?;
        Ok((identifier, k))
    }
}
impl Parser {
    fn parse_struct_declaration(&mut self) -> R<(Identifier, DeclarationKind)> {
        self.expect(TokenKind::Struct)?;
        let identifier = self.parse_identifier()?;
        let mut generics = self.parse_generics()?;
        generics.where_clause = self.parse_generic_where_clause()?;
        let variant = self.parse_variant_kind()?;

        match &variant {
            VariantKind::Unit | VariantKind::Tuple(..) => self.expect_line_break_or_semi()?,
            _ => {}
        }
        let s = Struct { generics, variant };
        let s = DeclarationKind::Struct(s);
        Ok((identifier, s))
    }

    fn parse_enum_declaration(&mut self) -> R<(Identifier, DeclarationKind)> {
        self.expect(TokenKind::Enum)?;
        let identifier = self.parse_identifier()?;
        let mut generics = self.parse_generics()?;
        generics.where_clause = self.parse_generic_where_clause()?;

        let variants =
            self.parse_delimiter_sequence(Delimiter::Brace, TokenKind::Comma, true, |p| {
                p.parse_enum_variant()
            })?;

        let e = Enum { generics, variants };

        Ok((identifier, DeclarationKind::Enum(e)))
    }
}

impl Parser {
    fn parse_interface(&mut self) -> R<(Identifier, DeclarationKind)> {
        // interface foo : bar where bar::element {}
        self.expect(TokenKind::Interface)?;
        let ident = self.parse_identifier()?;
        let mut generics = self.parse_generics()?;
        let extensions = if self.eat(TokenKind::Colon) {
            let paths =
                self.parse_sequence_until(&[], TokenKind::Comma, false, |p| p.parse_path())?;
            Some(paths)
        } else {
            None
        };
        generics.where_clause = self.parse_generic_where_clause()?;

        let declarations = self
            .parse_block_sequence(|p| p.parse_declaration(true, DeclarationContext::Interface))?
            .into_iter()
            .flatten()
            .collect();

        let interface = Interface {
            declarations,
            extensions,
            generics,
        };

        Ok((ident, DeclarationKind::Interface(interface)))
    }
}

impl Parser {
    fn parse_extern(&mut self) -> R<DeclarationKind> {
        self.expect(TokenKind::Extern)?;

        let abi = self.parse_string_content()?;

        let span = self.previous().unwrap().span;

        let declarations = self
            .parse_block_sequence(|p| p.parse_declaration(true, DeclarationContext::Extern))?
            .into_iter()
            .flatten()
            .collect();

        let e = Extern {
            abi,
            span,
            declarations,
        };

        let k = DeclarationKind::Extern(e);

        Ok(k)
    }
}

impl Parser {
    fn parse_extend(&mut self) -> R<DeclarationKind> {
        self.expect(TokenKind::Extend)?;
        let mut generics = self.parse_generics()?;
        let ty = self.parse_path()?;

        generics.where_clause = self.parse_generic_where_clause()?;

        let declarations = self
            .parse_block_sequence(|p| p.parse_declaration(true, DeclarationContext::Extend))?
            .into_iter()
            .flatten()
            .collect();

        let extend = Extend {
            ty,
            generics,
            declarations,
        };

        Ok(DeclarationKind::Extend(extend))
    }
    fn parse_conform(&mut self) -> R<DeclarationKind> {
        self.expect(TokenKind::Conform)?;
        let mut generics = self.parse_generics()?;

        let ty = self.parse_path()?;

        self.expect(TokenKind::Colon)?;

        let interface = self.parse_path()?;

        generics.where_clause = self.parse_generic_where_clause()?;

        let declarations = self
            .parse_block_sequence(|p| p.parse_declaration(true, DeclarationContext::Interface))?
            .into_iter()
            .flatten()
            .collect();

        let conform = Conform {
            ty,
            interface,
            generics,
            declarations,
        };

        Ok(DeclarationKind::Conform(conform))
    }
}

impl Parser {
    fn parse_bridge(&mut self) -> R<(Identifier, DeclarationKind)> {
        self.expect(TokenKind::Bridge)?;
        let ident = self.parse_identifier()?;

        let body = self.parse_bridge_body();

        Ok((ident, DeclarationKind::Bridge(body?)))
    }

    fn parse_bridge_body(&mut self) -> R<Bridge> {
        let values = self.parse_block_sequence(|p| p.parse_bridge_value())?;

        let mut map = HashMap::new();
        for (ident, value) in values.into_iter() {
            map.insert(ident, value);
        }

        let b = Bridge { values: map };

        Ok(b)
    }

    fn parse_bridge_value(&mut self) -> R<(Symbol, BridgeValue)> {
        let key = self.parse_string_content()?;

        self.expect(TokenKind::Assign)?;

        let value = match self.current_kind() {
            TokenKind::String => BridgeValue::String(self.parse_string_content()?),
            TokenKind::LBracket => {
                let items = self.parse_delimiter_sequence(
                    Delimiter::Bracket,
                    TokenKind::Comma,
                    true,
                    |p| p.parse_string_content(),
                )?;

                BridgeValue::Array(items)
            }
            TokenKind::LBrace => {
                let value = self.parse_bridge_body()?;
                BridgeValue::Dict(Box::new(value))
            }
            _ => {
                let msg = format!("expected bridge value, got {} instead", self.current_kind());
                let err = SpannedMessage::new(msg, self.current_token_span());
                return Err(err);
            }
        };
        Ok((key, value))
    }
}

impl Parser {
    fn parse_namespace(&mut self) -> R<(Identifier, DeclarationKind)> {
        self.expect(TokenKind::Namespace)?;
        let ident = self.parse_identifier()?;
        let declarations = self
            .parse_block_sequence(|p| p.parse_declaration(true, DeclarationContext::Interface))?
            .into_iter()
            .flatten()
            .collect();

        let namespace = Namespace { declarations };
        Ok((ident, DeclarationKind::Namespace(namespace)))
    }
}

impl Parser {
    fn parse_use_declaration(&mut self, is_import: bool) -> R<DeclarationKind> {
        /*
         * import foo::bar::baz;
         * import foo::bar::baz as foo;
         * import foo::bar::{baz, bar}
         */

        /*
         * export foo::bar::baz;
         * export foo::bar::baz as foo;
         * export foo::bar::{baz, bar}
         */

        if is_import {
            self.expect(TokenKind::Import)?;
        } else {
            self.expect(TokenKind::Export)?;
        }

        let path_tree = self.parse_path_tree()?;

        match &path_tree.node {
            PathTreeNode::Simple { .. } | PathTreeNode::Glob => {
                self.expect_line_break_or_semi()?;
            }
            PathTreeNode::Nested { .. } => {}
        }

        if is_import {
            Ok(DeclarationKind::Import(path_tree))
        } else {
            Ok(DeclarationKind::Export(path_tree))
        }
    }

    fn parse_path_tree(&mut self) -> R<PathTree> {
        let lo = self.lo_span();
        // collect module path
        let root = self.parse_module_path()?;

        // foo::bar::* | foo::bar::{X, Y, Z}
        let node = if self.eat(TokenKind::Scope) {
            self.parse_path_tree_glob_or_nested()?
        } else {
            // foo::bar | foo::bar as baz
            PathTreeNode::Simple {
                alias: self.parse_path_tree_alias()?,
            }
        };
        let span = lo.to(self.hi_span());
        Ok(PathTree { root, node, span })
    }

    fn parse_path_tree_glob_or_nested(&mut self) -> R<PathTreeNode> {
        if self.eat(TokenKind::Star) {
            Ok(PathTreeNode::Glob)
        } else {
            let lo = self.lo_span();
            let nodes = self.parse_path_tree_node_list()?;
            let span = lo.to(self.hi_span());
            let node = PathTreeNode::Nested { nodes, span };
            Ok(node)
        }
    }

    fn parse_path_tree_node_list(&mut self) -> R<Vec<PathTree>> {
        self.parse_delimiter_sequence(Delimiter::Brace, TokenKind::Comma, true, |this| {
            this.parse_path_tree()
        })
    }

    fn parse_path_tree_alias(&mut self) -> R<Option<Identifier>> {
        if !self.eat(TokenKind::As) {
            return Ok(None);
        }

        return Ok(Some(self.parse_identifier()?));
    }
}

impl Parser {
    fn parse_mod_declaration(&mut self) -> R<(Identifier, DeclarationKind)> {
        self.expect(TokenKind::Mod)?;
        let identifier = self.parse_identifier()?;
        self.expect_line_break_or_semi()?;
        Ok((identifier, DeclarationKind::Module(ModuleKind::Unloaded)))
    }
}

impl Parser {
    fn parse_computed_variable(&mut self) -> R<(Identifier, DeclarationKind)> {
        self.expect(TokenKind::Var)?;
        let identifier = self.parse_identifier()?;
        self.expect(TokenKind::Colon)?;
        let ty = self.parse_type()?;

        let block = if self.matches(TokenKind::LBrace) {
            Some(self.parse_block()?)
        } else {
            None
        };

        let kind = DeclarationKind::Computed(ComputedVariable { ty, block });

        return Ok((identifier, kind));
    }
}
