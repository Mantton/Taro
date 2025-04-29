use super::package::{Parser, R};
use crate::restrictions::Modifiers;
use std::collections::HashMap;
use taroc_ast::{
    AssociatedType, BindingPatternKind, Bridge, BridgeValue, Declaration, DeclarationContext,
    DeclarationKind, DefinedType, DefinedTypeKind, EnumCase, Extend, Extern, Generics, Local,
    Mutability, Namespace, PathTree, PathTreeNode, TypeAlias,
};
use taroc_ast_ir::LocalSource;
use taroc_span::{Identifier, SpannedMessage, Symbol};
use taroc_token::{Delimiter, TokenKind};

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
        let mut modifiers = Modifiers::empty();
        let static_span = if self.eat(TokenKind::Static) {
            modifiers.insert(Modifiers::STATIC);
            self.previous().map(|f| f.span)
        } else {
            None
        };

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

        let mut decl = Declaration {
            span: start_span.to(self.hi_span()),
            identifier,
            kind,
            visibility,
            attributes,
        };

        if modifiers.contains(Modifiers::STATIC) {
            match &mut decl.kind {
                DeclarationKind::Variable(local) => {
                    local.source = if matches!(context, DeclarationContext::Struct) {
                        LocalSource::StaticProperty
                    } else {
                        local.source
                    }
                }
                DeclarationKind::Function(node) => node.signature.is_static = true,
                _ if let Some(span) = static_span => {
                    let message = "`static` is not allowed on this declaration";
                    return Err(SpannedMessage::new(message.into(), span));
                }
                _ => unreachable!("ICE: static span must not be null"),
            }
        }

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
            TokenKind::Let => self.parse_variable_decl(context)?,
            TokenKind::Var => self.parse_variable_decl(context)?,
            TokenKind::Const => self.parse_const_decl()?,
            TokenKind::Import => (
                Identifier::emtpy(self.file.file),
                self.parse_use_declaration(true)?,
            ),
            TokenKind::Export => (
                Identifier::emtpy(self.file.file),
                self.parse_use_declaration(false)?,
            ),
            TokenKind::AssociatedType => self.parse_associated_type()?,
            TokenKind::Type => self.parse_type_declaration()?,
            TokenKind::Struct | TokenKind::Enum | TokenKind::Interface => {
                self.parse_defined_type()?
            }
            TokenKind::Function => self.parse_function()?,
            TokenKind::Init => (Identifier::emtpy(self.file.file), self.parse_constructor()?),
            TokenKind::Extern => (Identifier::emtpy(self.file.file), self.parse_extern()?),
            TokenKind::Extend => (Identifier::emtpy(self.file.file), self.parse_extend()?),
            TokenKind::Bridge => self.parse_bridge()?,
            TokenKind::Namespace => self.parse_namespace()?,
            TokenKind::Case => (
                Identifier::emtpy(self.file.file),
                self.parse_enum_case_decl()?,
            ),
            TokenKind::Operator => (Identifier::emtpy(self.file.file), self.parse_operator()?),
            _ => return Ok(None),
        };

        Ok(Some((identifier, kind)))
    }
}

impl Parser {
    fn parse_variable_decl(
        &mut self,
        context: DeclarationContext,
    ) -> R<(Identifier, DeclarationKind)> {
        let mutability = if self.eat(TokenKind::Let) {
            Mutability::Immutable
        } else if self.eat(TokenKind::Var) {
            Mutability::Mutable
        } else {
            unreachable!()
        };

        let pattern = self.parse_binding_pat()?;
        let ident =
            match pattern.kind {
                BindingPatternKind::Identifier(identifier) => identifier,
                _ => return Err(SpannedMessage::new(
                    "Top Level Variables and Constants MUST use Identifier Binding Pattern Only"
                        .into(),
                    pattern.span,
                )),
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
            source: if matches!(context, DeclarationContext::Struct) {
                LocalSource::StoredProperty
            } else {
                LocalSource::TopLevelDecl
            },
        };

        self.expect_line_break_or_semi()?;

        return Ok((ident, DeclarationKind::Variable(local)));
    }

    fn parse_const_decl(&mut self) -> R<(Identifier, DeclarationKind)> {
        let identifier = self.parse_identifier()?;
        self.expect(TokenKind::Colon)?;
        let ty = self.parse_type()?;
        self.expect(TokenKind::Assign)?;
        let value = self.parse_anon_const()?;
        self.expect_line_break_or_semi()?;
        let kind = DeclarationKind::Constant(ty, value);
        return Ok((identifier, kind));
    }
}

impl Parser {
    fn parse_type_declaration(&mut self) -> R<(Identifier, DeclarationKind)> {
        self.expect(TokenKind::Type)?;
        let identifier = self.parse_identifier()?;

        let type_parameters = self.parse_type_parameters()?;
        let ty = if self.eat(TokenKind::Assign) {
            Some(self.parse_type()?)
        } else {
            None
        };

        let where_clause = self.parse_generic_where_clause()?;

        let generics = Generics {
            type_parameters,
            where_clause,
            inheritance: None,
        };

        let decl = TypeAlias { ty, generics };

        let k = DeclarationKind::TypeAlias(decl);
        self.expect_line_break_or_semi()?;
        Ok((identifier, k))
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
        let ty = self.parse_type()?;
        let inheritance = self.parse_inheritance()?;
        let where_clause = self.parse_generic_where_clause()?;

        let declarations = self
            .parse_block_sequence(|p| p.parse_declaration(true, DeclarationContext::Extend))?
            .into_iter()
            .flatten()
            .collect();

        let generics = Generics {
            type_parameters: None,
            where_clause,
            inheritance,
        };

        let extend = Extend {
            ty,
            declarations,
            generics,
        };

        Ok(DeclarationKind::Extend(extend))
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
    fn parse_associated_type(&mut self) -> R<(Identifier, DeclarationKind)> {
        self.expect(TokenKind::AssociatedType)?;
        let identifier = self.parse_identifier()?;

        let inheritance = self.parse_inheritance()?;

        let default = if self.eat(TokenKind::Assign) {
            Some(self.parse_type()?)
        } else {
            None
        };

        let where_clause = self.parse_generic_where_clause()?;

        let generics = Generics {
            type_parameters: None,
            where_clause,
            inheritance,
        };

        return Ok((
            identifier,
            DeclarationKind::AssociatedType(AssociatedType { generics, default }),
        ));
    }
}

impl Parser {
    fn parse_defined_type(&mut self) -> R<(Identifier, DeclarationKind)> {
        let kind = if self.eat(TokenKind::Struct) {
            DefinedTypeKind::Struct
        } else if self.eat(TokenKind::Enum) {
            DefinedTypeKind::Enum
        } else if self.eat(TokenKind::Interface) {
            DefinedTypeKind::Interface
        } else {
            let msg = format!(
                "expected struct, enum or interface definition, got {} instead",
                self.current_kind()
            );
            let err = SpannedMessage::new(msg, self.current_token_span());
            return Err(err);
        };

        let identifier = self.parse_identifier()?;
        let type_parameters = self.parse_type_parameters()?;
        let inheritance = self.parse_inheritance()?;
        let where_clause = self.parse_generic_where_clause()?;

        let declarations = self
            .parse_block_sequence(|p| p.parse_declaration(true, DeclarationContext::Interface))?
            .into_iter()
            .flatten()
            .collect();

        let generics = Generics {
            inheritance,
            type_parameters,
            where_clause,
        };

        let node = DefinedType {
            kind,
            declarations,
            generics,
        };

        let kind = DeclarationKind::DefinedType(node);
        return Ok((identifier, kind));
    }
}

impl Parser {
    fn parse_enum_case_decl(&mut self) -> R<DeclarationKind> {
        self.expect(TokenKind::Case)?;
        let members = self.parse_sequence(TokenKind::Comma, |this| this.parse_enum_variant())?;
        let kind = DeclarationKind::EnumCase(EnumCase { members });
        return Ok(kind);
    }
}
