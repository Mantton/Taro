use super::package::{Parser, R};
use std::collections::HashMap;
use taroc_ast::{
    AssociatedDeclaration, AssociatedDeclarationKind, BindingPatternKind, Bridge, BridgeValue,
    ConstantDeclaration, Declaration, DeclarationKind, EnumDefinition, Extend, Extern,
    ForeignDeclaration, ForeignDeclarationKind, FunctionDeclaration, FunctionDeclarationKind,
    Generics, InterfaceDefinition, Local, Mutability, Namespace, PathTree, PathTreeNode,
    StructDefinition, TypeAlias, VariantKind,
};
use taroc_span::{Identifier, SpannedMessage, Symbol};
use taroc_token::{Delimiter, TokenKind};

pub struct FnParseMode {
    pub req_body: bool,
}

impl Parser {
    pub fn parse_module_declarations(&mut self) -> R<Vec<Declaration>> {
        let mut items = vec![];
        loop {
            let Some(item) = self.parse_declaration()? else {
                break;
            };

            items.push(item);
        }

        if !self.is_at_end() {
            let msg = format!(
                "expected top-level declaration, found '{}'",
                self.current_kind()
            );
            let err = SpannedMessage::new(msg, self.current_token_span());
            return Err(err);
        }

        return Ok(items);
    }

    pub fn parse_declaration(&mut self) -> R<Option<Declaration>> {
        let declaration = self.parse_declaration_internal(FnParseMode { req_body: true })?;
        let Some(declaration) = declaration else {
            return Ok(declaration);
        };

        match &declaration.kind {
            DeclarationKind::Operator(..) => {
                let message = "operator functions not allowed here".into();
                self.emit_error(message, declaration.span);
                return Ok(None);
            }
            _ => return Ok(Some(declaration)),
        }
    }

    fn parse_declaration_internal(&mut self, fn_mode: FnParseMode) -> R<Option<Declaration>> {
        self.consume_comments_and_new_lines();
        let start_span = self.lo_span();
        let attributes = self.parse_attributes()?;
        let visibility = self.parse_visibility()?;

        let Some((identifier, kind)) = self.parse_decl_kind(fn_mode)? else {
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

    fn parse_decl_list<T>(
        &mut self,
        mut action: impl FnMut(&mut Parser) -> R<Option<T>>,
    ) -> R<Vec<T>> {
        self.expect(TokenKind::LBrace)?;

        let mut decls = vec![];

        while !self.matches(TokenKind::RBrace) && !self.is_at_end() {
            self.consume_comments_and_new_lines();
            if self.matches(TokenKind::RBrace) {
                break;
            }
            match action(self)? {
                Some(decl) => decls.push(decl),
                None => {
                    let msg = format!("expected declaration, found '{}'", self.current_kind());
                    let err = SpannedMessage::new(msg, self.current_token_span());
                    return Err(err);
                }
            }

            if self.matches(TokenKind::RBrace) {
                break;
            }
        }
        self.expect(TokenKind::RBrace)?;

        return Ok(decls);
    }
}

impl Parser {
    fn parse_foreign_declaration(&mut self) -> R<Option<ForeignDeclaration>> {
        let mode = FnParseMode { req_body: false };
        let result = self.parse_declaration_internal(mode)?;

        let Some(result) = result else {
            return Ok(None);
        };

        let item = match ForeignDeclarationKind::try_from(result.kind) {
            Ok(kind) => {
                let declaration = Declaration {
                    span: result.span,
                    identifier: result.identifier,
                    kind,
                    visibility: result.visibility,
                    attributes: result.attributes,
                };

                Some(declaration)
            }
            Err(_) => {
                let message = "this declaration kind is not allowed in extern blocks".into();
                self.emit_error(message, result.span);
                return Ok(None);
            }
        };

        return Ok(item);
    }

    fn parse_associated_declaration(
        &mut self,
        fn_mode: FnParseMode,
    ) -> R<Option<AssociatedDeclaration>> {
        let result = self.parse_declaration_internal(fn_mode)?;
        let Some(result) = result else {
            return Ok(None);
        };

        let kind = match AssociatedDeclarationKind::try_from(result.kind) {
            Ok(kind) => kind,
            Err(_) => {
                let message =
                    "this declaration kind is not allowed in `interface` or `extend` blocks".into();
                self.emit_error(message, result.span);
                return Ok(None);
            }
        };

        let declaration = Declaration {
            span: result.span,
            identifier: result.identifier,
            kind,
            visibility: result.visibility,
            attributes: result.attributes,
        };

        return Ok(Some(declaration));
    }

    pub fn parse_function_declaration(&mut self) -> R<Option<FunctionDeclaration>> {
        let mode = FnParseMode { req_body: true };
        let result = self.parse_declaration_internal(mode)?;

        let Some(result) = result else {
            return Ok(None);
        };

        let kind = match FunctionDeclarationKind::try_from(result.kind) {
            Ok(kind) => kind,
            Err(_) => {
                let message = "this declaration kind is not allowed in function blocks".into();
                self.emit_error(message, result.span);
                return Ok(None);
            }
        };

        let declaration = FunctionDeclaration {
            span: result.span,
            identifier: result.identifier,
            kind,
            visibility: result.visibility,
            attributes: result.attributes,
        };

        return Ok(Some(declaration));
    }
}

impl Parser {
    fn parse_decl_kind(&mut self, mode: FnParseMode) -> R<Option<(Identifier, DeclarationKind)>> {
        let current_kind = self.current_kind();
        let (identifier, kind) = match current_kind {
            TokenKind::Struct => self.parse_struct_declaration()?,
            TokenKind::Enum => self.parse_enum_declaration()?,
            TokenKind::Interface => self.parse_interface()?,
            TokenKind::Var | TokenKind::Let => self.parse_variable_decl()?,
            TokenKind::Const => self.parse_const_decl()?,
            TokenKind::Import => (
                Identifier::emtpy(self.file.file),
                self.parse_use_declaration(true)?,
            ),
            TokenKind::Export => (
                Identifier::emtpy(self.file.file),
                self.parse_use_declaration(false)?,
            ),
            TokenKind::Type => self.parse_type_declaration()?,
            TokenKind::Function => self.parse_function(mode)?,
            TokenKind::Extern => (Identifier::emtpy(self.file.file), self.parse_extern()?),
            TokenKind::Extend => (Identifier::emtpy(self.file.file), self.parse_extend()?),
            TokenKind::Bridge => self.parse_bridge()?,
            TokenKind::Namespace => self.parse_namespace()?,
            TokenKind::Operator => self.parse_operator(mode)?,
            _ => return Ok(None),
        };

        Ok(Some((identifier, kind)))
    }
}

impl Parser {
    fn parse_variable_decl(&mut self) -> R<(Identifier, DeclarationKind)> {
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
        };

        self.expect_line_break_or_semi()?;

        return Ok((ident, DeclarationKind::Variable(local)));
    }

    fn parse_const_decl(&mut self) -> R<(Identifier, DeclarationKind)> {
        let identifier = self.parse_identifier()?;
        self.expect(TokenKind::Colon)?;
        let ty = self.parse_type()?;
        self.expect(TokenKind::Assign)?;

        let expr = if self.eat(TokenKind::Assign) {
            Some(self.parse_expression()?)
        } else {
            None
        };

        self.expect_line_break_or_semi()?;

        let decl = ConstantDeclaration {
            identifier,
            ty,
            expr,
        };

        let kind = DeclarationKind::Constant(decl);
        return Ok((identifier, kind));
    }
}

impl Parser {
    fn parse_type_declaration(&mut self) -> R<(Identifier, DeclarationKind)> {
        self.expect(TokenKind::Type)?;
        let identifier = self.parse_identifier()?;

        let type_parameters = self.parse_type_parameters()?;
        let conformances = self.parse_conformances()?;
        let ty = if self.eat(TokenKind::Assign) {
            Some(self.parse_type()?)
        } else {
            None
        };

        let where_clause = self.parse_generic_where_clause()?;

        let generics = Generics {
            type_parameters,
            where_clause,
            conformances,
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
        let abi = taroc_span::Spanned { span, value: abi };

        let declarations = self.parse_decl_list(|p| p.parse_foreign_declaration())?;

        let node = Extern { abi, declarations };
        let kind = DeclarationKind::Extern(node);
        Ok(kind)
    }
}

impl Parser {
    fn parse_extend(&mut self) -> R<DeclarationKind> {
        self.expect(TokenKind::Extend)?;
        let t_params = self.parse_type_parameters()?;
        if let Some(t_params) = t_params {
            self.emit_error("type aprameters are not supported on extension blocks, they would be inferred based on the type extended".into(), t_params.span);
        }

        let ty = self.parse_type()?;
        let conformances = self.parse_conformances()?;
        let where_clause = self.parse_generic_where_clause()?;

        let declarations = self
            .parse_decl_list(|p| p.parse_associated_declaration(FnParseMode { req_body: true }))?;

        let generics = Generics {
            type_parameters: None,
            where_clause,
            conformances,
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
        let declarations = self.parse_decl_list(|p| p.parse_declaration())?;

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
    fn parse_struct_declaration(&mut self) -> R<(Identifier, DeclarationKind)> {
        self.expect(TokenKind::Struct)?;
        let identifier = self.parse_identifier()?;
        let type_parameters = self.parse_type_parameters()?;
        let where_clause = self.parse_generic_where_clause()?;
        let generics = Generics {
            type_parameters,
            where_clause,
            conformances: None,
        };

        let variant = self.parse_variant_kind()?;

        match &variant {
            VariantKind::Unit | VariantKind::Tuple(..) => self.expect_line_break_or_semi()?,
            _ => {}
        }
        let s = StructDefinition { generics, variant };
        let s = DeclarationKind::Struct(s);
        Ok((identifier, s))
    }

    fn parse_enum_declaration(&mut self) -> R<(Identifier, DeclarationKind)> {
        self.expect(TokenKind::Enum)?;
        let identifier = self.parse_identifier()?;
        let type_parameters = self.parse_type_parameters()?;
        let where_clause = self.parse_generic_where_clause()?;
        let generics = Generics {
            type_parameters,
            where_clause,
            conformances: None,
        };

        let variants =
            self.parse_delimiter_sequence(Delimiter::Brace, TokenKind::Comma, true, |p| {
                p.parse_enum_variant()
            })?;

        let e = EnumDefinition { generics, variants };

        Ok((identifier, DeclarationKind::Enum(e)))
    }
}

impl Parser {
    fn parse_interface(&mut self) -> R<(Identifier, DeclarationKind)> {
        // interface foo : bar where bar::element {}
        self.expect(TokenKind::Interface)?;
        let ident = self.parse_identifier()?;

        let generics = {
            let type_parameters = self.parse_type_parameters()?;
            let where_clause = self.parse_generic_where_clause()?;
            let conformances = self.parse_conformances()?;

            Generics {
                type_parameters,
                where_clause,
                conformances,
            }
        };

        let declarations = self
            .parse_decl_list(|p| p.parse_associated_declaration(FnParseMode { req_body: false }))?;

        let interface = InterfaceDefinition {
            declarations,
            generics,
        };

        Ok((ident, DeclarationKind::Interface(interface)))
    }
}
