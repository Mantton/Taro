use crate::{
    ast::{
        self, AnonConst, AssociatedDeclaration, AssociatedDeclarationKind, Attribute,
        AttributeList, BinaryOperator, Block, ClosureExpression, ConformanceConstraint,
        Conformances, Constant, Declaration, DeclarationKind, Enum, EnumCase, Expression,
        ExpressionArgument, ExpressionField, ExpressionKind, Extension, FieldDefinition,
        ForStatement, Function, FunctionDeclaration, FunctionDeclarationKind, FunctionParameter,
        FunctionPrototype, FunctionSignature, GenericBound, GenericBounds, GenericRequirement,
        GenericRequirementList, GenericWhereClause, Generics, Identifier, IfExpression, Interface,
        Label, Literal, Local, MapPair, MatchArm, MatchExpression, Mutability, Namespace,
        NamespaceDeclaration, NamespaceDeclarationKind, NodeID, Operator, OperatorKind, Path,
        PathNode, PathSegment, Pattern, PatternBindingCondition, PatternKind, PatternPath,
        RequiredTypeConstraint, SelfKind, Statement, StatementKind, Struct, StructLiteral, Type,
        TypeAlias, TypeArgument, TypeArguments, TypeKind, TypeParameter, TypeParameterKind,
        TypeParameters, UnaryOperator, UseTree, UseTreeKind, UseTreeNestedItem, UseTreePath,
        Variant, VariantKind, Visibility, VisibilityLevel,
    },
    diagnostics::DiagCtx,
    error::ReportedError,
    parse::{Base, lexer, token::Token},
    span::{Position, Span, Spanned, Symbol},
};
use std::{cell::RefCell, collections::VecDeque, fmt::Display, rc::Rc};

type NextNode = Rc<RefCell<NodeTagger>>;
#[derive(Debug, Default)]
struct NodeTagger {
    next_index: u32,
}
impl NodeTagger {
    fn next(&mut self) -> NodeID {
        let id = NodeID::from_raw(self.next_index);
        self.next_index += 1;
        id
    }
}
pub fn parse_package(
    package: lexer::Pacakge,
    dcx: &DiagCtx,
) -> Result<ast::Package, ReportedError> {
    let next: NextNode = Default::default();
    let root = parse_module(package.root, next, dcx)?;
    Ok(ast::Package { root })
}

fn parse_module(
    module: lexer::Module,
    next: NextNode,
    dcx: &DiagCtx,
) -> Result<ast::Module, ReportedError> {
    let name = Symbol::new(&module.name);
    let mut files = vec![];
    let mut submodules = vec![];

    for file in module.files {
        let file = parse_file(file, next.clone(), dcx)?;
        files.push(file);
    }

    for module in module.submodules {
        let module = parse_module(module, next.clone(), dcx)?;
        submodules.push(module);
    }

    Ok(ast::Module {
        id: next.borrow_mut().next(),
        name,
        files,
        submodules,
    })
}

fn parse_file(
    file: lexer::File,
    next: NextNode,
    dcx: &DiagCtx,
) -> Result<ast::File, ReportedError> {
    let id = file.id;
    let parser = Parser::new(file, next.clone());
    let declarations = match parser.parse() {
        Ok(declarations) => declarations,
        Err(errors) => {
            for err in errors {
                dcx.emit_error(err.value.to_string(), Some(err.span));
            }
            return Err(ReportedError);
        }
    };

    Ok(ast::File { id, declarations })
}

type R<V> = Result<V, Spanned<ParserError>>;
struct Parser {
    file: lexer::File,
    cursor: usize,
    restrictions: Restrictions,
    anchors: VecDeque<usize>,
    next_index: NextNode,
    errors: Vec<Spanned<ParserError>>,
}

impl Parser {
    fn new(file: lexer::File, next: NextNode) -> Parser {
        Parser {
            file,
            cursor: 0,
            restrictions: Restrictions::empty(),
            anchors: VecDeque::new(),
            errors: vec![],
            next_index: next,
        }
    }
}

impl Parser {
    fn parse(mut self) -> Result<Vec<Declaration>, Vec<Spanned<ParserError>>> {
        let result = self.parse_module_declarations();
        match result {
            Ok(_) if !self.errors.is_empty() => return Err(self.errors),
            Ok(declarations) => return Ok(declarations),
            Err(error) => {
                self.errors.push(error);
                return Err(self.errors);
            }
        };
    }
}

impl Parser {
    fn current(&self) -> Option<Spanned<Token>> {
        if self.cursor >= self.file.tokens.len() {
            return None;
        }
        Some(self.file.tokens[self.cursor].clone())
    }

    fn previous(&self) -> Option<Spanned<Token>> {
        if self.cursor == 0 {
            return self.current();
        }
        if self.cursor - 1 >= self.file.tokens.len() {
            return None;
        }
        Some(self.file.tokens[self.cursor - 1].clone())
    }

    fn current_token(&self) -> Token {
        if let Some(token) = self.current() {
            return token.value;
        }
        Token::EOF
    }

    fn is_at_end(&self) -> bool {
        self.cursor >= self.file.tokens.len() - 1
    }

    fn bump(&mut self) {
        self.cursor += 1;
    }

    fn matches(&self, token: Token) -> bool {
        self.current_token() == token
    }

    fn matches_any(&self, tokens: &[Token]) -> bool {
        for token in tokens {
            if self.matches(token.clone()) {
                return true;
            }
        }
        return false;
    }

    fn matches_question(&self) -> bool {
        matches!(
            self.current_token(),
            Token::Question | Token::QuestionQuestion
        )
    }

    fn split_question_token(&mut self) {
        let Some(current) = self.current() else {
            return;
        };
        if current.value != Token::QuestionQuestion {
            return;
        }
        let span = current.span;
        let mid = Position {
            line: span.start.line,
            offset: span.start.offset + 1,
        };
        let first = Span {
            start: span.start,
            end: mid,
            file: span.file,
        };
        let second = Span {
            start: mid,
            end: span.end,
            file: span.file,
        };

        self.file.tokens[self.cursor] = Spanned::new(Token::Question, first);
        self.file
            .tokens
            .insert(self.cursor + 1, Spanned::new(Token::Question, second));
    }

    fn split_amp_token(&mut self) {
        let Some(current) = self.current() else {
            return;
        };
        if current.value != Token::AmpAmp {
            return;
        }
        let span = current.span;
        let mid = Position {
            line: span.start.line,
            offset: span.start.offset + 1,
        };
        let first = Span {
            start: span.start,
            end: mid,
            file: span.file,
        };
        let second = Span {
            start: mid,
            end: span.end,
            file: span.file,
        };

        self.file.tokens[self.cursor] = Spanned::new(Token::Amp, first);
        self.file
            .tokens
            .insert(self.cursor + 1, Spanned::new(Token::Amp, second));
    }

    fn eat_question(&mut self) -> bool {
        match self.current_token() {
            Token::Question => {
                self.bump();
                true
            }
            Token::QuestionQuestion => {
                self.split_question_token();
                self.bump();
                true
            }
            _ => false,
        }
    }

    fn eat_amp(&mut self) -> bool {
        match self.current_token() {
            Token::Amp => {
                self.bump();
                true
            }
            Token::AmpAmp => {
                self.split_amp_token();
                self.bump();
                true
            }
            _ => false,
        }
    }

    fn expect_question(&mut self) -> R<()> {
        if self.eat_question() {
            Ok(())
        } else {
            Err(self.err_at_current(ParserError::Expected(
                Token::Question,
                self.current_token(),
            )))
        }
    }

    fn expect_amp(&mut self) -> R<()> {
        if self.eat_amp() {
            Ok(())
        } else {
            Err(self.err_at_current(ParserError::Expected(
                Token::Amp,
                self.current_token(),
            )))
        }
    }

    fn eat(&mut self, token: Token) -> bool {
        if self.matches(token) {
            self.bump();
            return true;
        }

        false
    }

    fn next(&mut self, index: usize) -> Option<Token> {
        let k = self.cursor + index;
        if k >= self.file.tokens.len() {
            return None;
        }

        return Some(self.file.tokens[k].value.clone());
    }

    fn next_matches(&mut self, index: usize, token: Token) -> bool {
        let Some(tok) = self.next(index) else {
            return false;
        };

        tok == token
    }
    fn expect(&mut self, token: Token) -> R<()> {
        if self.eat(token.clone()) {
            Ok(())
        } else {
            return Err(self.err_at_current(ParserError::Expected(token, self.current_token())));
        }
    }

    #[track_caller]
    #[inline]
    fn expect_semi(&mut self) -> R<()> {
        if self.eat(Token::Semicolon) {
            return Ok(());
        } else {
            return Err(self.err_at_current(ParserError::ExpectedSemiColon));
        }
    }

    fn err_at_current(&self, err: ParserError) -> Spanned<ParserError> {
        Spanned::new(err, self.lo_span())
    }
}

impl Parser {
    fn next_id(&mut self) -> NodeID {
        self.next_index.borrow_mut().next()
    }
}

impl Parser {
    fn emit_warning(&mut self, _err: ParserError, _span: Span) {}
    fn emit_error(&mut self, err: ParserError, span: Span) {
        self.errors.push(Spanned::new(err, span));
    }
}
impl Parser {
    fn lo_span(&self) -> Span {
        self.current()
            .map(|token| token.span)
            .unwrap_or(Span::empty(self.file.id))
    }

    fn hi_span(&self) -> Span {
        self.previous()
            .map(|token| token.span)
            .unwrap_or(Span::empty(self.file.id))
    }
}

impl Parser {
    fn parse_module_declarations(&mut self) -> R<Vec<Declaration>> {
        let mut items = vec![];
        loop {
            let Some(item) = self.parse_declaration()? else {
                break;
            };

            items.push(item);
        }

        if !self.is_at_end() {
            return Err(self.err_at_current(ParserError::ExpectedTopLevelDeclaration));
        }

        return Ok(items);
    }

    fn parse_declaration(&mut self) -> R<Option<Declaration>> {
        let declaration = self.parse_declaration_internal(FnParseMode { req_body: true })?;

        let Some(declaration) = declaration else {
            return Ok(declaration);
        };

        match &declaration.kind {
            DeclarationKind::Operator(..) => {
                return Err(self.err_at_current(ParserError::TopLevelOperatorNotAllowed));
            }

            _ => return Ok(Some(declaration)),
        }
    }

    fn parse_declaration_internal(&mut self, fn_mode: FnParseMode) -> R<Option<Declaration>> {
        let start_span = self.lo_span();
        let attributes = self.parse_attributes()?;
        let visibility = self.parse_visibility()?;
        let Some((identifier, kind)) = self.parse_declaration_kind(fn_mode)? else {
            return Ok(None);
        };

        let declaration = Declaration {
            id: self.next_id(),
            span: start_span.to(self.hi_span()),
            identifier,
            kind,
            visibility,
            attributes,
        };

        self.expect_semi()?;
        Ok(Some(declaration))
    }

    fn parse_declaration_list<T>(
        &mut self,
        mut action: impl FnMut(&mut Parser) -> R<Option<T>>,
    ) -> R<Vec<T>> {
        self.expect(Token::LBrace)?;

        let mut decls = vec![];

        while !self.matches(Token::RBrace) && !self.is_at_end() {
            if self.matches(Token::RBrace) {
                break;
            }
            match action(self)? {
                Some(decl) => decls.push(decl),
                None => {
                    return Err(self.err_at_current(ParserError::ExpectedDeclaration));
                }
            }

            if self.matches(Token::RBrace) {
                break;
            }
        }
        self.expect(Token::RBrace)?;

        return Ok(decls);
    }
}

impl Parser {
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
                self.emit_error(ParserError::DissallowedAssociatedDeclaration, result.span);
                return Ok(None);
            }
        };

        let declaration = Declaration {
            id: result.id,
            span: result.span,
            identifier: result.identifier,
            kind,
            visibility: result.visibility,
            attributes: result.attributes,
        };

        return Ok(Some(declaration));
    }

    fn parse_function_declaration(&mut self) -> R<Option<FunctionDeclaration>> {
        let mode = FnParseMode { req_body: true };
        let result = self.parse_declaration_internal(mode)?;

        let Some(result) = result else {
            return Ok(None);
        };

        let kind = match FunctionDeclarationKind::try_from(result.kind) {
            Ok(kind) => kind,
            Err(_) => {
                self.emit_error(ParserError::DissallowedFunctionDeclaration, result.span);

                return Ok(None);
            }
        };

        let declaration = FunctionDeclaration {
            id: result.id,
            span: result.span,
            identifier: result.identifier,
            kind,
            visibility: result.visibility,
            attributes: result.attributes,
        };

        return Ok(Some(declaration));
    }

    fn parse_namespace_declaration(&mut self) -> R<Option<NamespaceDeclaration>> {
        let mode = FnParseMode { req_body: true };
        let result = self.parse_declaration_internal(mode)?;

        let Some(result) = result else {
            return Ok(None);
        };

        let kind = match NamespaceDeclarationKind::try_from(result.kind) {
            Ok(kind) => kind,
            Err(_) => {
                self.emit_error(ParserError::DissallowedNamespaceDeclaration, result.span);

                return Ok(None);
            }
        };

        let declaration = NamespaceDeclaration {
            id: result.id,
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
    fn parse_declaration_kind(
        &mut self,
        mode: FnParseMode,
    ) -> R<Option<(Identifier, DeclarationKind)>> {
        let token = self.current_token();
        let (identifier, kind) = match token {
            Token::Struct => self.parse_struct_declaration()?,
            Token::Enum => self.parse_enum_declaration()?,
            Token::Interface => self.parse_interface()?,
            Token::Var | Token::Let => self.parse_variable_decl()?,
            Token::Const => self.parse_const_decl()?,
            Token::Import => (
                Identifier::emtpy(self.file.id),
                self.parse_import_export_declaration(true)?,
            ),
            Token::Export => (
                Identifier::emtpy(self.file.id),
                self.parse_import_export_declaration(false)?,
            ),
            Token::Extern => (Identifier::emtpy(self.file.id), self.parse_extern_block()?),
            Token::Type => self.parse_type_declaration()?,
            Token::Function => self.parse_function(mode)?,
            Token::Extend => (Identifier::emtpy(self.file.id), self.parse_impl()?),
            Token::Namespace => self.parse_namespace()?,
            Token::Operator => self.parse_operator(mode)?,
            _ => return Ok(None),
        };

        Ok(Some((identifier, kind)))
    }
}

impl Parser {
    fn parse_extern_block(&mut self) -> R<DeclarationKind> {
        self.expect(Token::Extern)?;
        let abi = match self.current_token() {
            Token::String { value } => {
                self.bump();
                Symbol::new(&value)
            }
            _ => return Err(self.err_at_current(ParserError::ExpectedExternAbiString)),
        };

        let declarations: Vec<Declaration<ast::ExternDeclarationKind>> =
            if self.matches(Token::LBrace) {
                self.parse_declaration_list(|p| p.parse_extern_declaration(abi))?
            } else {
                vec![]
            };

        Ok(DeclarationKind::ExternBlock(ast::ExternBlock {
            abi,
            declarations,
        }))
    }

    fn parse_extern_declaration(
        &mut self,
        abi: Symbol,
    ) -> R<Option<Declaration<ast::ExternDeclarationKind>>> {
        let mode = FnParseMode { req_body: false };
        let result = self.parse_declaration_internal(mode)?;
        let Some(result) = result else {
            return Ok(None);
        };

        let kind = match ast::ExternDeclarationKind::try_from(result.kind) {
            Ok(mut kind) => {
                let ast::ExternDeclarationKind::Function(func) = &mut kind;
                if func.block.is_some() {
                    self.emit_error(ParserError::ExternFunctionBodyNotAllowed, result.span);
                    func.block = None;
                }
                func.abi = Some(abi);
                kind
            }
            Err(_) => {
                self.emit_error(ParserError::DissallowedExternDeclaration, result.span);
                return Ok(None);
            }
        };

        Ok(Some(Declaration {
            id: result.id,
            span: result.span,
            identifier: result.identifier,
            kind,
            visibility: result.visibility,
            attributes: result.attributes,
        }))
    }
}

impl Parser {
    fn parse_import_export_declaration(&mut self, is_import: bool) -> R<DeclarationKind> {
        if is_import {
            self.expect(Token::Import)?;
        } else {
            self.expect(Token::Export)?;
        }

        let path = self.parse_use_tree()?;

        if is_import {
            Ok(DeclarationKind::Import(path))
        } else {
            Ok(DeclarationKind::Export(path))
        }
    }

    fn parse_use_tree(&mut self) -> R<UseTree> {
        let lo = self.lo_span();
        let path = self.parse_use_tree_path()?;

        let kind = if self.eat(Token::DotStar) {
            UseTreeKind::Glob
        } else if self.eat(Token::Dot) {
            self.parse_use_tree_nested()?
        } else {
            UseTreeKind::Simple {
                alias: self.parse_use_tree_alias()?,
            }
        };

        let tree = UseTree {
            span: lo.to(self.hi_span()),
            path,
            kind,
        };

        Ok(tree)
    }

    fn parse_use_tree_path(&mut self) -> R<UseTreePath> {
        let start = self.lo_span();
        let mut nodes = vec![];

        loop {
            let identifier = self.parse_identifier()?;
            nodes.push(identifier);
            let is_coupler = (self.matches(Token::Dot) && self.next_matches(1, Token::LBrace))
                || self.matches(Token::DotStar);

            if is_coupler || !self.eat(Token::Dot) {
                break;
            } else {
                continue;
            }
        }

        let path = UseTreePath {
            span: start.to(self.hi_span()),
            nodes,
        };

        Ok(path)
    }

    fn parse_use_tree_nested(&mut self) -> R<UseTreeKind> {
        let lo = self.lo_span();
        let nodes = self.parse_delimiter_sequence(Delimiter::Brace, Token::Comma, |this| {
            this.parse_use_tree_nested_item()
        })?;

        let node = UseTreeKind::Nested {
            nodes,
            span: lo.to(self.hi_span()),
        };
        Ok(node)
    }

    fn parse_use_tree_nested_item(&mut self) -> R<UseTreeNestedItem> {
        let name = self.parse_identifier()?;
        let alias = self.parse_use_tree_alias()?;

        return Ok(UseTreeNestedItem {
            id: self.next_id(),
            name,
            alias,
        });
    }

    fn parse_use_tree_alias(&mut self) -> R<Option<Identifier>> {
        if !self.eat(Token::As) {
            return Ok(None);
        }

        return Ok(Some(self.parse_identifier()?));
    }
}

impl Parser {
    fn parse_namespace(&mut self) -> R<(Identifier, DeclarationKind)> {
        self.expect(Token::Namespace)?;
        let ident = self.parse_identifier()?;
        let declarations: Vec<Declaration<NamespaceDeclarationKind>> =
            if self.matches(Token::LBrace) {
                self.parse_declaration_list(|p| p.parse_namespace_declaration())?
            } else {
                vec![]
            };
        let namespace = Namespace { declarations };
        Ok((ident, DeclarationKind::Namespace(namespace)))
    }
}

impl Parser {
    fn parse_variable_decl(&mut self) -> R<(Identifier, DeclarationKind)> {
        let mutability = if self.eat(Token::Let) {
            Mutability::Immutable
        } else if self.eat(Token::Var) {
            Mutability::Mutable
        } else {
            unreachable!()
        };

        let pattern = self.parse_pattern()?;
        let ident = match &pattern.kind {
            PatternKind::Identifier(identifier) => identifier.clone(),
            _ => {
                return Err(Spanned::new(
                    ParserError::RequiredIdentifierPattern,
                    pattern.span,
                ));
            }
        };

        let ty = if self.eat(Token::Colon) {
            Some(self.parse_type()?)
        } else {
            None
        };

        let initializer = if self.eat(Token::Assign) {
            Some(self.parse_expression()?)
        } else {
            None
        };

        let local = Local {
            id: self.next_id(),
            mutability,
            pattern,
            ty,
            initializer,
            is_shorthand: false,
        };

        return Ok((ident, DeclarationKind::Variable(local)));
    }

    fn parse_const_decl(&mut self) -> R<(Identifier, DeclarationKind)> {
        self.expect(Token::Const)?;
        let identifier = self.parse_identifier()?;
        self.expect(Token::Colon)?;
        let ty = self.parse_type()?;

        let expr = if self.eat(Token::Assign) {
            Some(self.parse_expression()?)
        } else {
            None
        };

        let decl = Constant {
            identifier: identifier,
            ty,
            expr,
        };

        let kind = DeclarationKind::Constant(decl);
        return Ok((identifier, kind));
    }
}

impl Parser {
    fn parse_type_declaration(&mut self) -> R<(Identifier, DeclarationKind)> {
        self.expect(Token::Type)?;
        let identifier = self.parse_identifier()?;

        let type_parameters = self.parse_type_parameters()?;

        let bounds = if self.eat(Token::Colon) {
            let conformances = self.parse_generic_bounds()?;
            Some(conformances)
        } else {
            None
        };

        let ty = if self.eat(Token::Assign) {
            Some(self.parse_type()?)
        } else {
            None
        };

        let where_clause = self.parse_generic_where_clause()?;

        let generics = Generics {
            type_parameters,
            where_clause,
        };

        let decl = TypeAlias {
            ty,
            generics,
            bounds,
        };

        let k = DeclarationKind::TypeAlias(decl);
        Ok((identifier, k))
    }
}

impl Parser {
    fn parse_impl(&mut self) -> R<DeclarationKind> {
        self.expect(Token::Extend)?;
        let type_parameters = self.parse_type_parameters()?;

        let ty = self.parse_type()?;
        let conformances = self.parse_conformances()?;

        let where_clause = self.parse_generic_where_clause()?;

        let declarations = self.parse_declaration_list(|p| {
            p.parse_associated_declaration(FnParseMode { req_body: true })
        })?;

        let generics = Generics {
            type_parameters,
            where_clause,
        };

        let extend = Extension {
            ty,
            declarations,
            generics,
            conformances,
        };

        Ok(DeclarationKind::Extension(extend))
    }
}

impl Parser {
    fn parse_struct_declaration(&mut self) -> R<(Identifier, DeclarationKind)> {
        self.expect(Token::Struct)?;
        let identifier = self.parse_identifier()?;
        let type_parameters = self.parse_type_parameters()?;
        let where_clause = self.parse_generic_where_clause()?;
        let generics = Generics {
            type_parameters,
            where_clause,
        };

        let fields = self.parse_field_definitions(Delimiter::Brace)?;

        let s = Struct { generics, fields };
        let s = DeclarationKind::Struct(s);
        Ok((identifier, s))
    }

    fn parse_enum_declaration(&mut self) -> R<(Identifier, DeclarationKind)> {
        self.expect(Token::Enum)?;
        let identifier = self.parse_identifier()?;
        let type_parameters = self.parse_type_parameters()?;
        let where_clause = self.parse_generic_where_clause()?;
        let generics = Generics {
            type_parameters,
            where_clause,
        };

        let cases = self.parse_delimiter_sequence(Delimiter::Brace, Token::Semicolon, |this| {
            this.parse_enum_case()
        })?;
        let e = Enum { generics, cases };
        Ok((identifier, DeclarationKind::Enum(e)))
    }
}

impl Parser {
    fn parse_interface(&mut self) -> R<(Identifier, DeclarationKind)> {
        // interface foo : bar where bar::element {}
        self.expect(Token::Interface)?;
        let ident = self.parse_identifier()?;

        let generics = {
            let type_parameters = self.parse_type_parameters()?;
            let where_clause = self.parse_generic_where_clause()?;

            Generics {
                type_parameters,
                where_clause,
            }
        };

        let conformances = self.parse_conformances()?;

        let declarations = self.parse_declaration_list(|p| {
            p.parse_associated_declaration(FnParseMode { req_body: false })
        })?;

        let interface = Interface {
            declarations,
            generics,
            conformances,
        };

        Ok((ident, DeclarationKind::Interface(interface)))
    }
}

impl Parser {
    fn parse_identifier(&mut self) -> R<Identifier> {
        let Some(current) = self.current() else {
            return Err(self.err_at_current(ParserError::ExpectedIdentifier));
        };

        let span = current.span;
        match current.value {
            Token::Identifier { value: symbol } => {
                let v = Identifier {
                    span,
                    symbol: Symbol::new(&symbol),
                };
                self.bump();
                return Ok(v);
            }
            _ => {
                return Err(self.err_at_current(ParserError::ExpectedIdentifier));
            }
        };
    }

    fn parse_member_identifier(&mut self) -> R<Identifier> {
        let Some(current) = self.current() else {
            return Err(self.err_at_current(ParserError::ExpectedIdentifier));
        };

        let span = current.span;
        match current.value {
            Token::Identifier { value: symbol } => {
                let v = Identifier {
                    span,
                    symbol: Symbol::new(&symbol),
                };
                self.bump();
                Ok(v)
            }
            Token::Init => {
                let v = Identifier {
                    span,
                    symbol: Symbol::new("init"),
                };
                self.bump();
                Ok(v)
            }
            _ => Err(self.err_at_current(ParserError::ExpectedIdentifier)),
        }
    }

    fn parse_optional_identifier(&mut self) -> R<Option<Identifier>> {
        if matches!(self.current_token(), Token::Identifier { .. }) {
            return Ok(Some(self.parse_identifier()?));
        } else {
            return Ok(None);
        }
    }

    fn parse_mutability(&mut self) -> Mutability {
        if self.eat(Token::Mut) {
            Mutability::Mutable
        } else if self.eat(Token::Const) {
            Mutability::Immutable
        } else {
            Mutability::Immutable
        }
    }
}

impl Parser {
    fn parse_attributes(&mut self) -> R<AttributeList> {
        let mut attrs = vec![];
        while !self.is_at_end() {
            let Some(attr) = self.parse_attribute()? else {
                break;
            };

            attrs.push(attr);
        }

        self.eat(Token::Semicolon);
        Ok(attrs)
    }

    fn parse_attribute(&mut self) -> R<Option<Attribute>> {
        // NOTE: Nested attributes like @available("Platform-iOS") are not yet implemented
        if !self.eat(Token::At) {
            return Ok(None);
        };

        let identifier = self.parse_identifier()?;
        let attr = Attribute { identifier };
        return Ok(Some(attr));
    }
}

impl Parser {
    fn parse_visibility(&mut self) -> R<Visibility> {
        let lo = self.lo_span();
        let level = if self.eat(Token::Public) {
            VisibilityLevel::Public
        } else if self.eat(Token::Private) {
            VisibilityLevel::Private
        } else {
            VisibilityLevel::Inherent
        };

        Ok(Visibility {
            span: lo.to(self.hi_span()),
            level,
        })
    }
}

// Adt
impl Parser {
    fn parse_field_definition(&mut self) -> R<FieldDefinition> {
        let lo = self.lo_span();
        let visibility = self.parse_visibility()?;

        let mutability = if self.eat(Token::Readonly) {
            Mutability::Immutable
        } else {
            Mutability::Mutable
        };

        let identifier = self.parse_identifier()?;
        self.expect(Token::Colon)?;

        let ty = self.parse_type()?;
        let fd = FieldDefinition {
            id: self.next_id(),
            visibility,
            label: None,
            identifier,
            ty,
            mutability,
            span: lo.to(self.hi_span()),
        };

        Ok(fd)
    }

    fn parse_field_definitions(&mut self, delim: Delimiter) -> R<Vec<FieldDefinition>> {
        self.parse_delimiter_sequence(delim, Token::Semicolon, |p| p.parse_field_definition())
    }
}

impl Parser {
    fn parse_enum_case(&mut self) -> R<EnumCase> {
        let lo = self.lo_span();
        self.expect(Token::Case)?;
        let variants = self.parse_sequence(Token::Comma, |this| this.parse_enum_variant())?;

        Ok(EnumCase {
            span: lo.to(self.hi_span()),
            variants,
        })
    }
    fn parse_enum_variant(&mut self) -> R<Variant> {
        let lo = self.lo_span();
        let identifier = self.parse_identifier()?;
        let kind = self.parse_variant_kind()?;
        let discriminant = if self.eat(Token::Assign) {
            Some(self.parse_anon_const()?)
        } else {
            None
        };

        let v = Variant {
            id: self.next_id(),
            ctor_id: self.next_id(),
            identifier,
            kind,
            discriminant,
            span: lo.to(self.hi_span()),
        };

        Ok(v)
    }

    fn parse_variant_kind(&mut self) -> R<VariantKind> {
        match self.current_token() {
            Token::LParen => self.parse_tuple_variant(),
            _ => Ok(VariantKind::Unit),
        }
    }

    fn parse_tuple_variant(&mut self) -> R<VariantKind> {
        let fields = self.parse_delimiter_sequence(Delimiter::Parenthesis, Token::Comma, |p| {
            p.parse_tuple_variant_field()
        })?;

        let k = VariantKind::Tuple(fields);
        Ok(k)
    }

    fn parse_tuple_variant_field(&mut self) -> R<FieldDefinition> {
        let lo = self.lo_span();
        let vis = self.parse_visibility()?;

        let mutability = if self.eat(Token::Readonly) {
            Mutability::Immutable
        } else {
            Mutability::Mutable
        };

        let label = self.parse_label()?;
        let ty = self.parse_type()?;

        let def = FieldDefinition {
            id: self.next_id(),
            visibility: vis,
            label,
            mutability,
            identifier: Identifier::emtpy(self.file.id),
            ty,
            span: lo.to(self.hi_span()),
        };

        Ok(def)
    }
}

// Type
impl Parser {
    fn parse_type(&mut self) -> R<Box<Type>> {
        let lo = self.lo_span();
        let k = self.parse_type_kind()?;
        let hi = self.hi_span();
        let mut ty = Type {
            id: self.next_id(),
            span: lo.to(hi),
            kind: k,
        };

        // optional type : T?
        while self.matches_question() {
            let k = self.parse_optional_type(ty)?;
            let hi = self.hi_span();
            ty = Type {
                id: self.next_id(),
                span: lo.to(hi),
                kind: k,
            };
        }

        Ok(Box::new(ty))
    }

    fn parse_type_kind(&mut self) -> R<TypeKind> {
        let res = match self.current_token() {
            Token::Star => self.parse_pointer_type(Token::Star),
            Token::Amp | Token::AmpAmp => self.parse_pointer_type(Token::Amp),
            Token::Identifier { .. } => self.parse_identifier_type(),
            Token::LParen => self.parse_tuple_type(),
            Token::LBracket => self.parse_collection_type(),
            Token::Underscore => {
                self.bump();
                Ok(TypeKind::Infer)
            }
            Token::Any => {
                self.bump();
                let interfaces = self.parse_sequence(Token::Amp, |this| this.parse_path_node())?;
                Ok(TypeKind::BoxedExistential { interfaces })
            }
            _ => {
                return Err(self.err_at_current(ParserError::ExpectedType));
            }
        };

        res
    }

    fn parse_identifier_type(&mut self) -> R<TypeKind> {
        let path = self.parse_path()?;
        let kind = TypeKind::Nominal(path);
        Ok(kind)
    }

    fn parse_pointer_type(&mut self, k: Token) -> R<TypeKind> {
        debug_assert!(matches!(k, Token::Star | Token::Amp));
        if matches!(k, Token::Star) {
            self.expect(Token::Star)?; // eat '*' symbol
        } else {
            self.expect_amp()?; // eat '&' symbol
        }
        let is_pointer = matches!(k, Token::Star);
        let mutability = self.parse_mutability();
        let ty = self.parse_type()?;

        let kind = if is_pointer {
            TypeKind::Pointer(ty, mutability)
        } else {
            TypeKind::Reference(ty, mutability)
        };

        Ok(kind)
    }

    fn parse_tuple_type(&mut self) -> R<TypeKind> {
        let elements =
            self.parse_delimiter_sequence(Delimiter::Parenthesis, Token::Comma, |p| {
                p.parse_type()
            })?;

        if self.matches(Token::RArrow) {
            self.expect(Token::RArrow)?;
            let output = self.parse_type()?;

            let kind = TypeKind::Function {
                inputs: elements,
                output,
            };

            return Ok(kind);
        }

        if elements.len() == 1 {
            let first = elements.into_iter().next().unwrap();
            return Ok(TypeKind::Parenthesis(first));
        }

        Ok(TypeKind::Tuple(elements))
    }

    fn parse_collection_type(&mut self) -> R<TypeKind> {
        // Parses [T], [T;N], [T:V], [T as V].Member[X]
        // eat opening bracket
        self.expect(Token::LBracket)?;
        let ty = self.parse_type()?;

        let kind = if self.eat(Token::RBracket) {
            return Ok(TypeKind::List(ty));
        } else if self.eat(Token::Colon) {
            let value = self.parse_type()?;
            TypeKind::Dictionary { key: ty, value }
        } else if self.eat(Token::Semicolon) {
            let len = self.parse_anon_const()?;
            TypeKind::Array {
                size: len,
                element: ty,
            }
        } else {
            return Err(self.err_at_current(ParserError::InvalidCollectionType));
        };

        self.expect(Token::RBracket)?;

        return Ok(kind);
    }

    fn parse_optional_type(&mut self, ty: Type) -> R<TypeKind> {
        self.expect_question()?;
        let k = TypeKind::Optional(Box::new(ty));
        Ok(k)
    }
}

// Generics
impl Parser {
    fn parse_type_arguments(&mut self) -> R<TypeArguments> {
        let lo = self.lo_span();
        let arguments = self.parse_delimiter_sequence(Delimiter::Bracket, Token::Comma, |p| {
            p.parse_type_argument()
        })?;

        let span = lo.to(self.hi_span());
        Ok(TypeArguments { span, arguments })
    }

    fn parse_type_argument(&mut self) -> R<TypeArgument> {
        match self.current_token() {
            Token::LBrace
            | Token::Integer { .. }
            | Token::Rune { .. }
            | Token::Float { .. }
            | Token::True
            | Token::False => {
                // const
                Ok(TypeArgument::Const(self.parse_anon_const()?))
            }
            _ => {
                let ty = self.parse_type()?;
                Ok(TypeArgument::Type(ty))
            }
        }
    }

    fn parse_optional_type_arguments(&mut self) -> R<Option<TypeArguments>> {
        if self.matches(Token::LBracket) && self.can_parse_type_arguments() {
            Ok(Some(self.parse_type_arguments()?))
        } else {
            Ok(None)
        }
    }
}

impl Parser {
    fn parse_type_parameters(&mut self) -> R<Option<TypeParameters>> {
        let lo = self.lo_span();
        if !self.matches(Token::LBracket) {
            return Ok(None);
        }

        let parameters = self.parse_delimiter_sequence(Delimiter::Bracket, Token::Comma, |p| {
            p.parse_type_parameter()
        })?;

        let t = TypeParameters {
            span: lo.to(self.hi_span()),
            parameters,
        };

        Ok(Some(t))
    }
    fn parse_type_parameter(&mut self) -> R<TypeParameter> {
        if self.matches(Token::Const) {
            self.parse_const_type_parameter()
        } else {
            self.parse_normal_type_parameter()
        }
    }

    fn parse_const_type_parameter(&mut self) -> R<TypeParameter> {
        let lo = self.lo_span();
        self.expect(Token::Const)?;
        let identifier = self.parse_identifier()?;
        self.expect(Token::Colon)?;
        let ty = self.parse_type()?;

        let default = if self.eat(Token::Assign) {
            Some(self.parse_anon_const()?)
        } else {
            None
        };

        let span = lo.to(self.hi_span());
        let kind = TypeParameterKind::Constant { ty, default };

        let tp = TypeParameter {
            id: self.next_id(),
            identifier,
            span,
            bounds: None,
            kind,
        };

        Ok(tp)
    }
    fn parse_normal_type_parameter(&mut self) -> R<TypeParameter> {
        let lo = self.lo_span();

        let identifier = self.parse_identifier()?;

        let bounds = if self.eat(Token::Colon) {
            Some(self.parse_generic_bounds()?)
        } else {
            None
        };

        let default = if self.eat(Token::Assign) {
            Some(self.parse_type()?)
        } else {
            None
        };

        let kind = TypeParameterKind::Type { default };

        let span = lo.to(self.hi_span());

        let tp = TypeParameter {
            id: self.next_id(),
            identifier,
            span,
            bounds,
            kind,
        };

        Ok(tp)
    }
}

impl Parser {
    fn parse_generic_bounds(&mut self) -> R<GenericBounds> {
        let bounds = self.parse_sequence(Token::Amp, |p| p.parse_generic_bound())?;
        Ok(bounds)
    }

    fn parse_generic_bound(&mut self) -> R<GenericBound> {
        Ok(GenericBound {
            path: self.parse_path_node()?,
        })
    }
}

impl Parser {
    fn parse_generic_where_clause(&mut self) -> R<Option<GenericWhereClause>> {
        let lo = self.lo_span();
        if !self.eat(Token::Where) {
            return Ok(None);
        }
        let requirements = self.parse_generic_requirements()?;
        let clause = GenericWhereClause {
            requirements,
            span: lo.to(self.hi_span()),
        };
        Ok(Some(clause))
    }

    fn parse_generic_requirements(&mut self) -> R<GenericRequirementList> {
        self.parse_sequence(Token::Comma, |p| p.parse_generic_requirement())
    }

    fn parse_generic_requirement(&mut self) -> R<GenericRequirement> {
        let lo = self.lo_span();
        let bounded_type = self.parse_type()?;
        let kind = if self.eat(Token::Eql) {
            let bound = self.parse_type()?;
            let kind = RequiredTypeConstraint {
                bounded_type,
                bound,
                span: lo.to(self.hi_span()),
            };
            GenericRequirement::SameTypeRequirement(kind)
        } else if self.eat(Token::Colon) {
            let bounds = self.parse_generic_bounds()?;
            let kind = ConformanceConstraint {
                bounded_type,
                bounds,
                span: lo.to(self.hi_span()),
            };
            GenericRequirement::ConformanceRequirement(kind)
        } else {
            return Err(self.err_at_current(ParserError::ExpectedGenericRequirement));
        };

        return Ok(kind);
    }
}

impl Parser {
    fn can_parse_type_arguments(&mut self) -> bool {
        self.with_anchor(|p| {
            let v = p.parse_type_arguments();

            if v.is_err() {
                return false;
            }

            let disambiguating = is_generic_type_disambiguating_token(p.current_token());
            disambiguating
        })
    }
}

impl Parser {
    fn parse_conformances(&mut self) -> R<Option<Conformances>> {
        if self.eat(Token::Colon) {
            let lo = self.lo_span();
            let bounds = self.parse_sequence(Token::Comma, |this| this.parse_path_node())?;
            let node = Conformances {
                bounds,
                span: lo.to(self.hi_span()),
            };
            Ok(Some(node))
        } else {
            Ok(None)
        }
    }
}

// Patterns
impl Parser {
    fn parse_match_arm_pattern(&mut self) -> R<Pattern> {
        let lo = self.lo_span();
        let cases =
            self.parse_sequence_until(&[Token::EqArrow], Token::Bar, |p| p.parse_pattern())?;

        if cases.is_empty() {
            return Err(self.err_at_current(ParserError::ExpectedMatchingPattern));
        }

        // has one pattern
        if cases.len() == 1 {
            return Ok(cases.into_iter().next().unwrap());
        }

        // has multiple patterns is an or pattern
        let span = lo.to(self.hi_span());
        let kind = PatternKind::Or(cases, span);

        let pat = Pattern {
            id: self.next_id(),
            span,
            kind,
        };

        Ok(pat)
    }

    fn parse_pattern(&mut self) -> R<Pattern> {
        let lo = self.lo_span();
        let k = self.parse_pattern_kind()?;

        let o = Pattern {
            id: self.next_id(),
            span: lo.to(self.hi_span()),
            kind: k,
        };

        Ok(o)
    }

    fn parse_pattern_kind(&mut self) -> R<PatternKind> {
        match self.current_token() {
            Token::LParen => self.parse_pattern_tuple_kind(),
            Token::Amp | Token::AmpAmp => self.parse_ref_pattern(),
            Token::Underscore => {
                self.bump();
                Ok(PatternKind::Wildcard)
            }
            Token::DotDot => {
                if !self.restrictions.contains(Restrictions::ALLOW_REST_PATTERN) {
                    self.emit_error(ParserError::DisallowedRestPatterns, self.lo_span());
                }
                self.bump();
                Ok(PatternKind::Rest)
            }
            Token::Dot | Token::Identifier { .. } => self.parse_pattern_path_kind(),
            _ => {
                let ac = self.parse_anon_const()?;
                Ok(PatternKind::Literal(ac))
            }
        }
    }

    fn parse_pattern_tuple_kind(&mut self) -> R<PatternKind> {
        let lo = self.lo_span();
        let pats = self.parse_delimiter_sequence(Delimiter::Parenthesis, Token::Comma, |p| {
            p.parse_pattern()
        })?;
        Ok(PatternKind::Tuple(pats, lo.to(self.hi_span())))
    }

    fn parse_ref_pattern(&mut self) -> R<PatternKind> {
        self.expect_amp()?;
        let mutability = self.parse_mutability();
        let pattern = self.parse_pattern()?;
        Ok(PatternKind::Reference {
            pattern: Box::new(pattern),
            mutability,
        })
    }

    fn parse_pattern_path_kind(&mut self) -> R<PatternKind> {
        // Cannot Possibly be a path pattern
        if matches!(self.current_token(), Token::Identifier { .. })
            && !(self.next_matches(1, Token::Dot) | self.next_matches(1, Token::LParen))
        {
            let ident = self.parse_identifier()?;
            return Ok(PatternKind::Identifier(ident));
        }

        let path = self.parse_pattern_path()?;

        match self.current_token() {
            Token::LParen => {
                let lo = self.lo_span();

                let mut res = Restrictions::empty();
                res.insert(Restrictions::ALLOW_REST_PATTERN);
                let fields = self.with_restrictions(res, |p| {
                    p.parse_delimiter_sequence(Delimiter::Parenthesis, Token::Comma, |p| {
                        p.parse_pattern()
                    })
                })?;

                Ok(PatternKind::PathTuple {
                    path,
                    fields,
                    field_span: lo.to(self.hi_span()),
                })
            }
            _ => Ok(PatternKind::Member(path)),
        }
    }
    // Parse:
    //   .Case         => PatternPathHead::Inferred
    //   A(.B)*        => PatternPathHead::Qualifed
    pub fn parse_pattern_path(&mut self) -> R<PatternPath> {
        // Shorthand: `.Case`
        let lo = self.lo_span();
        if self.eat(Token::Dot) {
            let name = self.parse_identifier()?;
            let span = lo.to(self.hi_span());
            return Ok(PatternPath::Inferred { name, span });
        }

        // Full: A(.B)*
        let path = self.parse_path()?;
        Ok(PatternPath::Qualified { path })
    }
}

// Block
impl Parser {
    fn parse_block(&mut self) -> R<Block> {
        let lo = self.lo_span();
        let mut has_declarations = false;
        let statements = self.parse_block_sequence(|p| {
            let s = p.parse_statement()?;
            has_declarations = has_declarations || matches!(s.kind, StatementKind::Declaration(..));
            Ok(s)
        })?;

        Ok(Block {
            id: self.next_id(),
            statements,
            span: lo.to(self.hi_span()),
            has_declarations,
        })
    }
}

// Statement
impl Parser {
    fn parse_statement(&mut self) -> R<Statement> {
        let lo = self.lo_span();
        let label = self.parse_label()?;
        let k = self.parse_statement_kind(label)?;

        let stmt = Statement {
            id: self.next_id(),
            kind: k,
            span: lo.to(self.hi_span()),
        };

        // Closing, we might not need the semi
        if !self.matches(Token::RBrace) && !matches!(&stmt.kind, StatementKind::Declaration(..)) {
            self.expect_semi()?;
        }

        Ok(stmt)
    }

    fn parse_statement_kind(&mut self, label: Option<Label>) -> R<StatementKind> {
        match self.current_token() {
            Token::Loop | Token::While | Token::For => {}
            _ => self.warn_improper_label_position(label.clone()),
        };

        match self.current_token() {
            Token::Let | Token::Var => self.parse_local_statement(),
            Token::Loop => self.parse_loop_stmt(label),
            Token::While => self.parse_while_stmt(label),
            Token::For => self.parse_for_stmt(label),
            Token::Return => self.parse_return_stmt(),
            Token::Break => self.parse_break_stmt(),
            Token::Continue => self.parse_continue_stmt(),
            Token::Defer => self.parse_defer_stmt(),
            Token::Guard => self.parse_guard_stmt(),
            _ => {
                // is decl
                if let Some(decl) = self.parse_function_declaration()? {
                    return Ok(StatementKind::Declaration(decl));
                }

                // is expr
                let expr = self.parse_expression()?;
                return Ok(StatementKind::Expression(expr));

                // invalid stmt
                // let msg = format!("expected statement found {}", self.current_token());
                // let span = self.current_token_span();
                // Err(SpannedMessage::new(msg, span))
            }
        }
    }

    fn warn_improper_label_position(&mut self, label: Option<Label>) {
        if let Some(label) = label {
            self.emit_warning(ParserError::DisallowedLabel, label.span);
        }
    }
}

impl Parser {
    fn parse_local(&mut self) -> R<Local> {
        // let | var <binding_pattern> <type_annotation>? <initializer_clause>?
        // type_annotation = : <type>
        // initializer_clause: = <expr>
        let mutability = if self.eat(Token::Let) {
            Mutability::Immutable
        } else if self.eat(Token::Var) {
            Mutability::Mutable
        } else {
            unreachable!("expected `let` | `var` token")
        };

        let pattern = self.parse_pattern()?;
        if !matches!(
            pattern.kind,
            PatternKind::Identifier(..) | PatternKind::Wildcard | PatternKind::Tuple(..)
        ) {
            return Err(Spanned::new(
                ParserError::DisallowedLocalBindingPattern,
                pattern.span,
            ));
        }

        let ty = if self.eat(Token::Colon) {
            Some(self.parse_type()?)
        } else {
            None
        };

        let initializer = if self.eat(Token::Assign) {
            Some(self.parse_expression()?)
        } else {
            None
        };

        let local = Local {
            id: self.next_id(),
            mutability,
            pattern,
            ty,
            initializer,
            is_shorthand: false,
        };

        Ok(local)
    }
    fn parse_local_statement(&mut self) -> R<StatementKind> {
        let local = self.parse_local()?;
        Ok(StatementKind::Variable(local))
    }
}

impl Parser {
    fn parse_loop_stmt(&mut self, label: Option<Label>) -> R<StatementKind> {
        self.expect(Token::Loop)?;
        let block = self.parse_block()?;
        Ok(StatementKind::Loop { label, block })
    }

    fn parse_while_stmt(&mut self, label: Option<Label>) -> R<StatementKind> {
        self.expect(Token::While)?;
        let while_restrictions =
            Restrictions::ALLOW_BINDING_CONDITION | Restrictions::NO_STRUCT_LITERALS;
        let condition = self.with_restrictions(while_restrictions, |p| p.parse_expression())?;
        let block = self.parse_block()?;

        Ok(StatementKind::While {
            label,
            condition,
            block,
        })
    }

    fn parse_for_stmt(&mut self, label: Option<Label>) -> R<StatementKind> {
        self.expect(Token::For)?;
        let pattern = self.parse_pattern()?;
        self.expect(Token::In)?;

        let for_restrictions = Restrictions::empty();

        let iterator = self.with_restrictions(for_restrictions, |p| p.parse_expression())?;

        let clause = if self.eat(Token::Where) {
            let clause = self.with_restrictions(for_restrictions, |p| p.parse_expression())?;
            Some(clause)
        } else {
            None
        };

        let block = self.parse_block()?;

        let f = ForStatement {
            label,
            pattern,
            iterator,
            clause,
            block,
        };
        Ok(StatementKind::For(f))
    }
}

impl Parser {
    fn parse_return_stmt(&mut self) -> R<StatementKind> {
        self.expect(Token::Return)?;

        if self.matches_any(&[Token::Semicolon, Token::RBrace]) {
            return Ok(StatementKind::Return(None));
        }

        let expr = Some(self.parse_expression()?);
        Ok(StatementKind::Return(expr))
    }

    fn parse_break_stmt(&mut self) -> R<StatementKind> {
        self.expect(Token::Break)?;
        let ident = self.parse_optional_identifier()?;
        Ok(StatementKind::Break(ident))
    }

    fn parse_continue_stmt(&mut self) -> R<StatementKind> {
        self.expect(Token::Continue)?;
        let ident = self.parse_optional_identifier()?;
        Ok(StatementKind::Continue(ident))
    }

    fn parse_defer_stmt(&mut self) -> R<StatementKind> {
        self.expect(Token::Defer)?;
        let block = self.parse_block()?;
        Ok(StatementKind::Defer(block))
    }

    fn parse_guard_stmt(&mut self) -> R<StatementKind> {
        self.expect(Token::Guard)?;

        let if_restrictions =
            Restrictions::ALLOW_BINDING_CONDITION | Restrictions::NO_STRUCT_LITERALS;
        let condition = self.with_restrictions(if_restrictions, |p| p.parse_expression())?;

        self.expect(Token::Else)?;
        let block = self.parse_block()?;

        Ok(StatementKind::Guard {
            condition,
            else_block: block,
        })
    }
}

// Sequences
impl Parser {
    fn parse_delimiter_sequence<T, F>(
        &mut self,
        delim: Delimiter,
        separator: Token,
        mut action: F,
    ) -> R<Vec<T>>
    where
        F: FnMut(&mut Parser) -> R<T>,
    {
        // eat open
        self.expect(delim.open())?;

        // if immediately closed return empty vec
        if self.eat(delim.close()) {
            return Ok(Vec::new());
        }

        let mut proceed = true;

        let mut items = Vec::new();
        while proceed {
            // parse item
            let item = action(self)?;
            items.push(item);

            proceed = self.eat(separator.clone());

            // can proceed but cursor points to ending token, exit loop
            if proceed && self.matches(delim.close()) {
                break;
            }
        }

        if self.matches(Token::Semicolon) {
            return Err(self.err_at_current(ParserError::UnexpectedSemicolonInList {
                context: "multiline list - add a trailing comma before the newline",
            }));
        }

        self.expect(delim.close())?;
        Ok(items)
    }

    fn parse_sequence_until<T, F>(
        &mut self,
        until: &[Token],
        separator: Token,
        mut action: F,
    ) -> R<Vec<T>>
    where
        F: FnMut(&mut Parser) -> R<T>,
    {
        let mut proceed = true;

        let mut items = Vec::new();
        while proceed {
            // parse item
            let item = action(self)?;
            items.push(item);

            proceed = self.eat(separator.clone());

            // can proceed but cursor points to ending token, exit loop
            if proceed && self.matches_any(until) {
                break;
            } else if self.matches_any(until) {
                break;
            }
        }

        Ok(items)
    }
}

impl Parser {
    fn parse_block_sequence<T, F>(&mut self, mut parse_action: F) -> R<Vec<T>>
    where
        F: FnMut(&mut Parser) -> R<T>,
    {
        self.expect(Token::LBrace)?;

        let mut items = vec![];

        while !self.matches(Token::RBrace) && !self.is_at_end() {
            if self.matches(Token::RBrace) {
                break;
            }
            let item = parse_action(self)?;
            items.push(item);

            if self.matches(Token::RBrace) {
                break;
            }
        }

        self.expect(Token::RBrace)?;
        Ok(items)
    }
}

impl Parser {
    fn parse_sequence<T, F>(&mut self, separator: Token, mut action: F) -> R<Vec<T>>
    where
        F: FnMut(&mut Parser) -> R<T>,
    {
        let mut proceed = true;
        let mut items = Vec::new();
        while proceed {
            let item = action(self)?;
            items.push(item);
            proceed = self.eat(separator.clone());
        }
        Ok(items)
    }
}

impl Parser {
    fn drop_anchor(&mut self) {
        self.anchors.push_back(self.cursor);
    }

    fn raise_anchor(&mut self) {
        let v = self.anchors.pop_back();
        if let Some(v) = v {
            self.cursor = v;
        }
    }

    fn with_anchor<T, F>(&mut self, mut action: F) -> T
    where
        F: FnMut(&mut Parser) -> T,
    {
        self.drop_anchor();
        let result = action(self);
        self.raise_anchor();

        result
    }
}

impl Parser {
    fn parse_label(&mut self) -> R<Option<Label>> {
        let can_parse = matches!(self.current_token(), Token::Identifier { .. })
            && self.next_matches(1, Token::Colon);
        if !can_parse {
            return Ok(None);
        }

        let lo = self.lo_span();

        let identifier = self.parse_identifier()?;
        self.expect(Token::Colon)?;

        let label = Label {
            identifier,
            span: lo.to(self.hi_span()),
        };

        Ok(Some(label))
    }
}

// Expressions
impl Parser {
    fn parse_expression(&mut self) -> R<Box<Expression>> {
        self.parse_assignment_expr()
    }

    fn parse_anon_const(&mut self) -> R<AnonConst> {
        let value = self.parse_expression()?;
        let a = AnonConst { value };
        Ok(a)
    }
}

impl Parser {
    fn build_expr(&mut self, kind: ExpressionKind, span: Span) -> Box<Expression> {
        Box::new(Expression {
            id: self.next_id(),
            kind,
            span,
        })
    }
}

impl Parser {
    fn parse_assignment_expr(&mut self) -> R<Box<Expression>> {
        let mut expr = self.parse_non_assignment_expr()?;

        use Token as T;

        if self.eat(Token::Assign) {
            let value = self.parse_non_assignment_expr()?;
            let span = expr.span.to(value.span);
            let kind = ExpressionKind::Assign(expr, value);
            expr = self.build_expr(kind, span);
        } else if matches!(
            self.current_token(),
            T::PlusEq
                | T::MinusEq
                | T::MulEq
                | T::DivEq
                | T::RemEq
                | T::AmpEq
                | T::BarEq
                | T::CaretEq
                | T::ShlEq
                | T::ShrEq
        ) {
            let op = Self::bin_op_assign(self.current_token()).unwrap();
            self.bump();

            let value = self.parse_non_assignment_expr()?;
            let span = expr.span.to(value.span);
            let kind = ExpressionKind::AssignOp(op, expr, value);
            expr = self.build_expr(kind, span);
        }

        Ok(expr)
    }
}

impl Parser {
    fn parse_non_assignment_expr(&mut self) -> R<Box<Expression>> {
        self.parse_pipe_expr()
    }

    fn parse_pipe_expr(&mut self) -> R<Box<Expression>> {
        let mut expr = self.parse_ternary_expr()?;

        while matches!(self.current_token(), Token::Pipe) {
            self.bump();
            let right = self.with_restrictions(Restrictions::ALLOW_WILDCARD, |this| {
                this.parse_ternary_expr()
            })?;

            let span = expr.span.to(right.span);
            let kind = ExpressionKind::Pipe(expr, right);
            expr = self.build_expr(kind, span);
        }

        Ok(expr)
    }

    fn parse_ternary_expr(&mut self) -> R<Box<Expression>> {
        let mut expr = self.parse_optional_default_expr()?;

        while self.eat(Token::Question) {
            let middle = self.parse_ternary_expr()?;

            self.expect(Token::Colon)?;

            let right = self.parse_ternary_expr()?;

            let span = expr.span.to(right.span);
            let kind = ExpressionKind::Ternary(expr, middle, right);
            expr = self.build_expr(kind, span);
        }

        Ok(expr)
    }
}

impl Parser {
    fn parse_optional_default_expr(&mut self) -> R<Box<Expression>> {
        let mut expr = self.parse_range_expr()?;
        while matches!(self.current_token(), Token::QuestionQuestion) {
            self.bump();
            let right = self.parse_range_expr()?;

            let span = expr.span.to(right.span);
            let kind = ExpressionKind::OptionalDefault(expr, right);
            expr = self.build_expr(kind, span);
        }
        Ok(expr)
    }
}

impl Parser {
    fn parse_range_expr(&mut self) -> R<Box<Expression>> {
        let mut expr = self.parse_bool_or_expr()?;
        let is_inclusive = if self.eat(Token::DotDot) {
            false
        } else if self.eat(Token::DotDotEq) {
            true
        } else {
            return Ok(expr);
        };

        let rhs = self.parse_bool_or_expr()?;

        let span = expr.span.to(rhs.span);
        let kind = ExpressionKind::Range(expr, rhs, is_inclusive);

        expr = self.build_expr(kind, span);
        Ok(expr)
    }
}

impl Parser {
    fn parse_bool_or_expr(&mut self) -> R<Box<Expression>> {
        // a || b
        let mut expr = self.parse_bool_and_expr()?;

        while matches!(self.current_token(), Token::BarBar) {
            expr = self.build_binary_expr(expr, |p| p.parse_bool_and_expr())?;
        }

        Ok(expr)
    }
    fn parse_bool_and_expr(&mut self) -> R<Box<Expression>> {
        // a && b
        let mut expr = self.parse_comparison_expr()?;

        while matches!(self.current_token(), Token::AmpAmp) {
            expr = self.build_binary_expr(expr, |p| p.parse_comparison_expr())?;
        }

        Ok(expr)
    }

    fn parse_comparison_expr(&mut self) -> R<Box<Expression>> {
        let mut expr = self.parse_bit_or_expr()?;

        while matches!(
            self.current_token(),
            Token::LChevron
                | Token::RChevron
                | Token::Geq
                | Token::Leq
                | Token::Neq
                | Token::Eql
                | Token::PtrEq
        ) {
            expr = self.build_binary_expr(expr, |p| p.parse_bit_or_expr())?;
        }

        Ok(expr)
    }
    fn parse_bit_or_expr(&mut self) -> R<Box<Expression>> {
        // a | b
        let mut expr = self.parse_bit_xor_expr()?;

        while matches!(self.current_token(), Token::Bar) {
            expr = self.build_binary_expr(expr, |p| p.parse_bit_xor_expr())?;
        }

        Ok(expr)
    }
    fn parse_bit_xor_expr(&mut self) -> R<Box<Expression>> {
        // boolean [a ^ b]

        let mut expr = self.parse_bit_and_expr()?;

        while matches!(self.current_token(), Token::Caret) {
            expr = self.build_binary_expr(expr, |p| p.parse_bit_and_expr())?;
        }

        Ok(expr)
    }
    fn parse_bit_and_expr(&mut self) -> R<Box<Expression>> {
        // boolean [&]

        let mut expr = self.parse_bit_shift_expr()?;

        while matches!(self.current_token(), Token::Amp) {
            expr = self.build_binary_expr(expr, |p| p.parse_bit_shift_expr())?;
        }

        Ok(expr)
    }
    fn parse_bit_shift_expr(&mut self) -> R<Box<Expression>> {
        // boolean [<< , >> ]
        let mut expr = self.parse_term_expr()?;

        while matches!(self.current_token(), Token::Shl | Token::Shr) {
            expr = self.build_binary_expr(expr, |p| p.parse_term_expr())?;
        }

        Ok(expr)
    }

    fn parse_term_expr(&mut self) -> R<Box<Expression>> {
        // boolean [ + - ]
        let mut expr = self.parse_factor_expr()?;

        while matches!(self.current_token(), Token::Minus | Token::Plus) {
            expr = self.build_binary_expr(expr, |p| p.parse_factor_expr())?;
        }

        Ok(expr)
    }

    fn parse_factor_expr(&mut self) -> R<Box<Expression>> {
        // boolean [ * , / , %]

        let mut expr = self.parse_cast_expr()?;

        while matches!(
            self.current_token(),
            Token::Quotient | Token::Star | Token::Modulus
        ) {
            expr = self.build_binary_expr(expr, |p| p.parse_cast_expr())?;
        }

        Ok(expr)
    }

    fn build_binary_expr<F>(&mut self, lhs: Box<Expression>, mut action: F) -> R<Box<Expression>>
    where
        F: FnMut(&mut Parser) -> R<Box<Expression>>,
    {
        let op = Self::bin_op_non_assign(self.current_token());

        let Some(op) = op else {
            return Err(self.err_at_current(ParserError::UnknownBinaryOperator));
        };

        self.bump(); // eat operator

        let rhs = action(self)?;
        let span = lhs.span.clone().to(rhs.span.clone());
        let kind = ExpressionKind::Binary(op, lhs, rhs);
        let expr = self.build_expr(kind, span);

        Ok(expr)
    }
}

impl Parser {
    fn parse_cast_expr(&mut self) -> R<Box<Expression>> {
        let mut expr = self.parse_kw_prefix_expr()?;

        while self.eat(Token::As) {
            let ty = self.parse_type()?;

            let span = expr.span.clone().to(ty.span.clone());
            let kind = ExpressionKind::CastAs(expr, ty);
            expr = self.build_expr(kind, span)
        }

        return Ok(expr);
    }
}

impl Parser {
    fn parse_kw_prefix_expr(&mut self) -> R<Box<Expression>> {
        // ensure <expr>
        // await <expr>
        return self.parse_prefix_expr();
    }
}

impl Parser {
    fn parse_prefix_expr(&mut self) -> R<Box<Expression>> {
        let lo = self.lo_span();
        // Expression Statements
        if (self.matches(Token::If) || self.matches(Token::Match))
            && !self
                .restrictions
                .contains(Restrictions::ALLOW_BINDING_CONDITION)
        {
            return self.parse_stmt_expr();
        }

        let operator = match self.current_token() {
            Token::Bang => {
                self.bump();
                UnaryOperator::LogicalNot
            }
            Token::Tilde => {
                self.bump();
                UnaryOperator::BitwiseNot
            }
            Token::Star => {
                self.bump();
                let expr = self.parse_prefix_expr()?;
                return Ok(
                    self.build_expr(ExpressionKind::Dereference(expr), lo.to(self.hi_span()))
                );
            }
            Token::Amp | Token::AmpAmp => {
                self.expect_amp()?;
                let mutability = self.parse_mutability();
                let expr = self.parse_prefix_expr()?;
                return Ok(self.build_expr(
                    ExpressionKind::Reference(expr, mutability),
                    lo.to(self.hi_span()),
                ));
            }
            Token::Minus => {
                self.bump();
                UnaryOperator::Negate
            }
            _ => return self.parse_postfix_expr(),
        };

        let mut expr = self.parse_prefix_expr()?;
        let kind = ExpressionKind::Unary(operator, expr);
        let span = lo.to(self.hi_span());
        expr = self.build_expr(kind, span);
        return Ok(expr);
    }
}

impl Parser {
    fn parse_postfix_expr_suffix(
        &mut self,
        mut expr: Box<Expression>,
        is_optional_chain: &mut bool,
    ) -> R<Box<Expression>> {
        let mut pre_consumed_dot = false;
        let mut seen_type_arguments = false;
        loop {
            let mut lo = self.lo_span();

            if pre_consumed_dot {
                lo = self.previous().unwrap().span;
            }

            // parsing dot expr: `foo.<expr>`
            if self.eat(Token::Dot) || pre_consumed_dot {
                pre_consumed_dot = false; // reset for next iter
                // parsing tuple index: `foo.<integer>`
                if matches!(
                    self.current_token(),
                    Token::Integer {
                        base: Base::Decimal,
                        ..
                    }
                ) {
                    let c = self.parse_literal()?;
                    let k = ExpressionKind::TupleAccess(expr, AnonConst { value: c });
                    let span = lo.to(self.hi_span());
                    expr = self.build_expr(k, span);
                    seen_type_arguments = false;
                    continue;
                }

                // field access: `foo.<ident>`
                let lo = expr.span;
                let kind = ExpressionKind::Member {
                    target: expr,
                    name: self.parse_member_identifier()?,
                };
                let span = lo.to(self.hi_span());
                expr = self.build_expr(kind, span);
                seen_type_arguments = false;
                continue;
            }

            // specialize: `Foo[T]`
            if self.matches(Token::LBracket) {
                if seen_type_arguments {
                    self.emit_error(ParserError::ExtraTypeArguments, self.lo_span());
                    return Err(self.err_at_current(ParserError::ExtraTypeArguments));
                }

                let args = self.parse_type_arguments()?;
                let kind = ExpressionKind::Specialize {
                    target: expr,
                    type_arguments: args,
                };
                let span = lo.to(self.hi_span());
                expr = self.build_expr(kind, span);
                seen_type_arguments = true;
                continue;
            }

            // parsing call expr: `foo(<expr_arguments>)`
            if self.matches(Token::LParen) {
                expr = self.parse_call_expr(expr)?;
                seen_type_arguments = false;
                continue;
            }

            // parsing optional access: `foo ?. <integer_literal> | <ident>`
            if self.eat(Token::QuestionDot) {
                *is_optional_chain = true;
                let span = expr.span.to(self.hi_span());

                let kind = ExpressionKind::OptionalUnwrap(expr);
                expr = self.build_expr(kind, lo.to(span));
                pre_consumed_dot = matches!(
                    self.current_token(),
                    Token::Identifier { .. }
                        | Token::Integer {
                            base: Base::Decimal,
                            ..
                        }
                );

                seen_type_arguments = false;
                continue;
            }

            expr = self.try_parse_struct_literal(expr)?;
            break;
        }
        Ok(expr)
    }

    fn parse_postfix_expr(&mut self) -> R<Box<Expression>> {
        let mut expr = self.parse_primary_expr()?;

        let mut has_optional_chain = false;

        expr = self.parse_postfix_expr_suffix(expr, &mut has_optional_chain)?;

        if has_optional_chain {
            let span = expr.span.clone();
            let node = ExpressionKind::OptionalEvaluation(expr);
            expr = self.build_expr(node, span);
        }

        Ok(expr)
    }
}

impl Parser {
    fn parse_pattern_binding_condition(&mut self) -> R<Box<Expression>> {
        if !self
            .restrictions
            .contains(Restrictions::ALLOW_BINDING_CONDITION)
        {
            return Err(self.err_at_current(ParserError::DisallowedBindingCondition));
        }

        let lo = self.lo_span();
        // case <pattern> = <expr>
        self.expect(Token::Case)?;
        let pattern = self.parse_pattern()?;
        self.expect(Token::Assign)?;
        let expression =
            self.with_restrictions(Restrictions::NO_STRUCT_LITERALS, |p| p.parse_expression())?;

        let span = lo.to(self.hi_span());
        let p = PatternBindingCondition {
            expression,
            pattern,
            span,
        };

        let kind = ExpressionKind::PatternBinding(p);
        let expr = self.build_expr(kind, span);
        Ok(expr)
    }

    fn parse_optional_binding_condition(&mut self) -> R<Box<Expression>> {
        if !self
            .restrictions
            .contains(Restrictions::ALLOW_BINDING_CONDITION)
        {
            return Err(self.err_at_current(ParserError::DisallowedBindingCondition));
        }

        let lo = self.lo_span();
        // let <ident> = <expr>
        self.expect(Token::Let)?;
        let identifier = self.parse_identifier()?;
        let pattern = Pattern {
            id: self.next_id(),
            span: identifier.span,
            kind: PatternKind::Identifier(identifier),
        };

        let expression = if self.eat(Token::Assign) {
            self.parse_expression()?
        } else {
            self.build_expr(ExpressionKind::Identifier(identifier), identifier.span)
        };

        let span = lo.to(self.hi_span());

        let p = PatternBindingCondition {
            expression,
            pattern,
            span,
        };

        let kind = ExpressionKind::OptionalPatternBinding(p);
        let expr = self.build_expr(kind, span);
        Ok(expr)
    }
}

impl Parser {
    fn parse_call_expr(&mut self, expr: Box<Expression>) -> R<Box<Expression>> {
        let args = self.parse_expression_argument_list(Delimiter::Parenthesis)?;
        let s = expr.span.clone();
        let k = ExpressionKind::Call(expr, args);
        return Ok(self.build_expr(k, s.to(self.hi_span())));
    }
}

impl Parser {
    fn parse_closure_expression(&mut self) -> R<Box<Expression>> {
        // |a| {} | || -> int {} | async || await ok()
        let lo = self.lo_span();
        let prototype = self.parse_closure_prototype()?;
        let signature = FunctionSignature {
            prototype,
            span: lo.to(self.hi_span()),
        };

        let body = self.parse_expression()?;

        let closure = ClosureExpression {
            signature,
            body,
            span: lo.to(self.hi_span()),
        };

        let kind = ExpressionKind::Closure(closure);
        let expr = self.build_expr(kind, lo);
        Ok(expr)
    }

    fn parse_closure_prototype(&mut self) -> R<FunctionPrototype> {
        let inputs = if self.eat(Token::BarBar) {
            Vec::new()
        } else {
            let params = self.parse_delimiter_sequence(Delimiter::Bar, Token::Comma, |p| {
                p.parse_closure_parameter()
            })?;
            params
        };

        let output = if self.eat(Token::RArrow) {
            Some(self.parse_type()?)
        } else {
            None
        };
        Ok(FunctionPrototype { inputs, output })
    }

    fn parse_closure_parameter(&mut self) -> R<FunctionParameter> {
        let lo = self.lo_span();
        let attributes = self.parse_attributes()?;

        let ident = self.parse_identifier()?;
        let mut is_variadic = false;
        let ty = if self.eat(Token::Colon) {
            let t = self.parse_type()?;
            is_variadic = self.eat(Token::Ellipsis);
            t
        } else {
            Box::new(Type {
                id: self.next_id(),
                span: ident.span.clone(),
                kind: TypeKind::InferedClosureParameter,
            })
        };

        let param = FunctionParameter {
            id: self.next_id(),
            attributes,
            label: None,
            name: ident,
            annotated_type: ty,
            default_value: None,
            is_variadic,
            span: lo.to(self.hi_span()),
        };

        Ok(param)
    }
}

impl Parser {
    fn parse_tuple_expr(&mut self) -> R<Box<Expression>> {
        let lo = self.lo_span();

        let items = self.parse_delimiter_sequence(Delimiter::Parenthesis, Token::Comma, |p| {
            p.parse_expression()
        })?;

        let span = lo.to(self.hi_span());

        let kind = if items.len() == 1 {
            ExpressionKind::Parenthesis(items.into_iter().next().unwrap())
        } else {
            ExpressionKind::Tuple(items)
        };

        let expr = self.build_expr(kind, span);
        Ok(expr)
    }
}

impl Parser {
    /// Parses a collection literal expression.
    ///
    /// Syntax:
    /// - `[]` → empty array
    /// - `[:]` → empty dictionary
    /// - `[a, b, c]` → array with elements
    /// - `[a: b, c: d]` → dictionary with key-value pairs
    /// - `[expr; count]` → repeat expression (array of `count` copies of `expr`)
    ///
    /// The parser determines array vs dictionary by looking at the first element:
    /// - If followed by `:`, it's a dictionary
    /// - If followed by `;`, it's a repeat expression
    /// - Otherwise, it's an array
    fn parse_collection_expr(&mut self) -> R<Box<Expression>> {
        let lo = self.lo_span();
        self.expect(Token::LBracket)?;

        // early return, []
        if self.eat(Token::RBracket) {
            let kind = ExpressionKind::Array(vec![]);
            let expr = self.build_expr(kind, lo.to(self.hi_span()));
            return Ok(expr);
        }

        // early return, [:]
        if self.matches(Token::Colon) && self.next_matches(1, Token::RBracket) {
            self.bump(); // eat colon
            self.bump(); // eat rbracket

            let kind = ExpressionKind::DictionaryLiteral(vec![]);
            let expr = self.build_expr(kind, lo.to(self.hi_span()));
            return Ok(expr);
        }

        let mut map_pairs = vec![];
        let mut array_elements = vec![];

        #[derive(Debug, PartialEq)]
        enum SS {
            Dict,
            Array,
        }

        // Parse first element
        let first_expr = self.parse_expression()?;

        // Repeat expression: [expr; count]
        if self.eat(Token::Semicolon) {
            let count = self.parse_anon_const()?;
            self.expect(Token::RBracket)?;
            let kind = ExpressionKind::Repeat {
                value: first_expr,
                count,
            };
            let expr = self.build_expr(kind, lo.to(self.hi_span()));
            return Ok(expr);
        }

        // Dictionary vs array detection based on colon
        let state = if self.eat(Token::Colon) {
            let value = self.parse_expression()?;
            map_pairs.push(MapPair {
                key: first_expr,
                value,
            });
            SS::Dict
        } else {
            array_elements.push(first_expr);
            SS::Array
        };

        // If there's a comma after the first element, parse remaining elements
        if self.eat(Token::Comma) && !self.matches(Token::RBracket) {
            let mut parser = |p: &mut Parser| -> R<()> {
                let k = p.parse_expression()?;

                match state {
                    SS::Array => {
                        array_elements.push(k);
                    }
                    SS::Dict => {
                        p.expect(Token::Colon)?;
                        let v = p.parse_expression()?;
                        let pair = MapPair { key: k, value: v };
                        map_pairs.push(pair);
                    }
                }
                Ok(())
            };

            let _ = self.parse_sequence_until(&[Token::RBracket], Token::Comma, |p| parser(p))?;
        }

        self.expect(Token::RBracket)?;

        let kind = match state {
            SS::Dict => ExpressionKind::DictionaryLiteral(map_pairs),
            SS::Array => ExpressionKind::Array(array_elements),
        };

        let expr = self.build_expr(kind, lo.to(self.hi_span()));
        return Ok(expr);
    }
}

impl Parser {
    fn parse_primary_expr(&mut self) -> R<Box<Expression>> {
        match self.current_token() {
            Token::Integer { .. }
            | Token::Float { .. }
            | Token::String { .. }
            | Token::Rune { .. }
            | Token::True
            | Token::False
            | Token::Nil => self.parse_literal(),
            Token::Identifier { .. } => self.parse_identifier_expression(),
            Token::Dot => self.parse_inferred_member_expression(),
            Token::LParen => self.parse_tuple_expr(),
            Token::LBracket => self.parse_collection_expr(),
            Token::Case => self.parse_pattern_binding_condition(),
            Token::Let => self.parse_optional_binding_condition(),
            Token::LBrace => self.parse_block_expression(),
            Token::Bar | Token::BarBar => self.parse_closure_expression(),
            Token::Underscore => {
                if !self.restrictions.contains(Restrictions::ALLOW_WILDCARD) {
                    self.emit_error(ParserError::DisallowedWildcardExpression, self.lo_span());
                }

                let lo = self.lo_span();
                let kind = ExpressionKind::Wildcard;
                self.bump();
                Ok(self.build_expr(kind, lo.to(self.hi_span())))
            }
            _ => return Err(self.err_at_current(ParserError::ExpectedExpression)),
        }
    }
}
impl Parser {
    fn parse_identifier_expression(&mut self) -> R<Box<Expression>> {
        let identifier = self.parse_identifier()?;
        let span = identifier.span;
        Ok(self.build_expr(ExpressionKind::Identifier(identifier), span))
    }
}
impl Parser {
    fn parse_inferred_member_expression(&mut self) -> R<Box<Expression>> {
        let lo = self.lo_span();
        self.expect(Token::Dot)?;
        let name = self.parse_member_identifier()?;
        let span = lo.to(self.hi_span());
        Ok(self.build_expr(ExpressionKind::InferredMember { name }, span))
    }

    fn parse_expression_argument_list(&mut self, delim: Delimiter) -> R<Vec<ExpressionArgument>> {
        self.parse_delimiter_sequence(delim, Token::Comma, |p| p.parse_expression_argument())
    }

    fn parse_expression_argument(&mut self) -> R<ExpressionArgument> {
        let lo = self.lo_span();
        let label = self.parse_label()?;
        let expression = self.parse_non_assignment_expr()?;
        let span = lo.to(self.hi_span());
        let arg = ExpressionArgument {
            label,
            expression,
            span,
        };

        Ok(arg)
    }
}
impl Parser {
    fn parse_stmt_expr(&mut self) -> R<Box<Expression>> {
        match self.current_token() {
            Token::If => self.parse_if_expr(),
            Token::Match => self.parse_match_expression(),
            _ => unreachable!("must manually check for token kind matching if | switch | match"),
        }
    }

    fn parse_block_expression(&mut self) -> R<Box<Expression>> {
        let block = self.parse_block()?;
        let span = block.span;
        let kind = ExpressionKind::Block(block);
        Ok(self.build_expr(kind, span))
    }
}

impl Parser {
    fn parse_if_expr(&mut self) -> R<Box<Expression>> {
        let lo = self.lo_span();

        self.expect(Token::If)?;

        // Conditions
        let if_restrictions =
            Restrictions::ALLOW_BINDING_CONDITION | Restrictions::NO_STRUCT_LITERALS;
        let condition = self.with_restrictions(if_restrictions, |p| p.parse_expression())?;

        // Then - Block
        let then_block = self.parse_block()?;
        let then_block_span = then_block.span;
        let then_block = self.build_expr(ExpressionKind::Block(then_block), then_block_span);

        // Else - Block
        let else_block = if self.eat(Token::Else) {
            let else_block = if self.matches(Token::If) {
                self.parse_if_expr()?
            } else if self.matches(Token::LBrace) {
                self.parse_block_expression()?
            } else {
                return Err(self.err_at_current(ParserError::ExpectedElseBlock));
            };

            Some(else_block)
        } else {
            None
        };

        let node = IfExpression {
            condition,
            then_block,
            else_block,
        };

        let k = ExpressionKind::If(node);
        Ok(self.build_expr(k, lo.to(self.hi_span())))
    }
}

impl Parser {
    fn parse_match_expression(&mut self) -> R<Box<Expression>> {
        let lo = self.lo_span();

        self.expect(Token::Match)?;

        let kw_span = self.previous().unwrap().span;
        let value =
            self.with_restrictions(Restrictions::NO_STRUCT_LITERALS, |p| p.parse_expression())?;

        let mut arms = vec![];
        self.expect(Token::LBrace)?;

        while !self.matches(Token::RBrace) && !self.is_at_end() {
            if self.matches(Token::RBrace) {
                break;
            }
            let item = self.parse_match_arm()?;
            arms.push(item);
            self.expect_semi()?;
        }

        self.expect(Token::RBrace)?;

        let node = MatchExpression {
            arms,
            value,
            kw_span,
        };
        let k = ExpressionKind::Match(node);
        Ok(self.build_expr(k, lo.to(self.hi_span())))
    }

    fn parse_match_arm(&mut self) -> R<MatchArm> {
        let lo = self.lo_span();

        // Allow `_ => ...` as shorthand for `case _ => ...`
        let is_wildcard_shorthand =
            self.matches(Token::Underscore) && self.next_matches(1, Token::EqArrow);
        if !is_wildcard_shorthand {
            self.expect(Token::Case)?;
        }
        let pattern = self.parse_match_arm_pattern()?;
        let guard = if self.eat(Token::If) {
            Some(self.parse_expression()?)
        } else {
            None
        };

        self.expect(Token::EqArrow)?;
        let body = self.parse_expression()?;
        let arm = MatchArm {
            pattern,
            body,
            guard,
            span: lo.to(self.hi_span()),
        };
        Ok(arm)
    }
}
impl Parser {
    fn parse_literal(&mut self) -> R<Box<Expression>> {
        let literal = match self.current_token() {
            Token::Integer { value, base } => Literal::Integer { value, base },
            Token::Float { value, .. } => Literal::Float { value },
            Token::String { value } => Literal::String { value },
            Token::Rune { value } => Literal::Rune { value },
            Token::True => Literal::Bool(true),
            Token::False => Literal::Bool(false),
            Token::Nil => Literal::Nil,
            _ => unreachable!(),
        };

        let k = ExpressionKind::Literal(literal);
        let expr = self.build_expr(k, self.lo_span());
        self.bump(); // consume token
        Ok(expr)
    }
}

// Functions
impl Parser {
    fn parse_function(&mut self, mode: FnParseMode) -> R<(Identifier, DeclarationKind)> {
        // func <name> <type_parameters>? (<parameter list>) <async?> -> <return_type>? <where_clause>?
        self.expect(Token::Function)?;
        let identifier = self.parse_identifier()?;
        let func = self.parse_fn(mode)?;
        Ok((identifier, DeclarationKind::Function(func)))
    }

    pub fn parse_operator(&mut self, mode: FnParseMode) -> R<(Identifier, DeclarationKind)> {
        self.expect(Token::Operator)?;
        let lo = self.lo_span();
        let kind = self.parse_operator_from_token()?;
        let span = lo.to(self.hi_span());
        let function = self.parse_fn(mode)?;
        Ok((
            Identifier::new(Symbol::new(""), span),
            DeclarationKind::Operator(Operator { kind, function }),
        ))
    }

    fn parse_fn(&mut self, mode: FnParseMode) -> R<Function> {
        let lo = self.lo_span();
        let type_parameters = self.parse_type_parameters()?;
        let parameters = self.parse_function_parameters()?;

        let return_type = if self.eat(Token::RArrow) {
            Some(self.parse_type()?)
        } else {
            None
        };

        let where_clause = self.parse_generic_where_clause()?;

        let prototype = FunctionPrototype {
            inputs: parameters,
            output: return_type,
        };

        let signature = FunctionSignature {
            span: lo.to(self.hi_span()),
            prototype,
        };

        let block = if self.matches(Token::LBrace) {
            Some(self.parse_block()?)
        } else {
            if mode.req_body {
                self.emit_error(
                    ParserError::FunctionBodyRequired,
                    self.previous().unwrap().span,
                );
            }
            None
        };

        let generics = Generics {
            type_parameters,
            where_clause,
        };

        let func = Function {
            signature,
            block,
            generics,
            abi: None,
        };

        Ok(func)
    }

    fn parse_function_parameters(&mut self) -> R<Vec<FunctionParameter>> {
        self.parse_delimiter_sequence(Delimiter::Parenthesis, Token::Comma, |p| {
            p.parse_function_parameter()
        })
    }
    fn parse_function_parameter(&mut self) -> R<FunctionParameter> {
        if let Some(self_param) = self.parse_self_parameter()? {
            return Ok(self_param);
        }

        let lo = self.lo_span();

        // @attribute label name: type
        let attributes = self.parse_attributes()?;

        let mut underscore_label = false;
        let label = if matches!(self.current_token(), Token::Identifier { .. }) {
            Some(self.parse_identifier()?)
        } else if self.matches(Token::Underscore) {
            underscore_label = true;
            self.bump();
            None
        } else {
            return Err(self.err_at_current(ParserError::ExpectedParameterNameOrLabel));
        };

        let name = if matches!(self.current_token(), Token::Identifier { .. }) {
            self.parse_identifier()?
        } else if let Some(label) = label {
            label
        } else if underscore_label {
            Identifier::emtpy(self.file.id)
        } else {
            return Err(self.err_at_current(ParserError::ExpectedParameterName));
        };

        self.expect(Token::Colon)?;
        let label = if let Some(label) = label {
            Some(Label {
                span: label.span.to(self.hi_span()),
                identifier: label,
            })
        } else {
            None
        };

        let ty = self.parse_type()?;

        let is_variadic = self.eat(Token::Ellipsis);

        let default_value = if self.eat(Token::Assign) {
            let expr = self.parse_expression()?;
            Some(expr)
        } else {
            None
        };

        let param = FunctionParameter {
            id: self.next_id(),
            attributes,
            label,
            name,
            annotated_type: ty,
            default_value,
            is_variadic,
            span: lo.to(self.hi_span()),
        };

        Ok(param)
    }

    fn parse_self_parameter(&mut self) -> R<Option<FunctionParameter>> {
        let lo = self.lo_span();
        let attributes = self.parse_attributes()?;

        let (kind, mutability, ident) = match self.current_token() {
            Token::Identifier { .. } => {
                let anchor = self.cursor;
                let ident = self.parse_identifier()?;

                if ident.symbol.as_str() == "self" {
                    (SelfKind::Copy, Mutability::Immutable, ident)
                } else {
                    self.cursor = anchor;
                    return Ok(None);
                }
            }
            Token::Amp | Token::AmpAmp => {
                self.expect_amp()?;
                let mutability = self.parse_mutability();
                (SelfKind::Reference, mutability, self.parse_self()?)
            }
            _ => return Ok(None),
        };

        let self_ty = Type {
            id: self.next_id(),
            span: ident.span,
            kind: TypeKind::ImplicitSelf,
        };

        let ty = match kind {
            SelfKind::Copy => self_ty,
            SelfKind::Reference => Type {
                id: self.next_id(),
                span: ident.span,
                kind: TypeKind::Reference(Box::new(self_ty), mutability),
            },
        };

        Ok(Some(FunctionParameter {
            id: self.next_id(),
            attributes,
            label: None,
            name: ident,
            annotated_type: Box::new(ty),
            default_value: None,
            is_variadic: false,
            span: lo.to(self.hi_span()),
        }))
    }

    fn parse_self(&mut self) -> R<Identifier> {
        let ident = self.parse_identifier()?;

        if ident.symbol.as_str() != "self" {
            return Err(self.err_at_current(ParserError::ExpectedSelf));
        }

        return Ok(ident);
    }
}

impl Parser {
    pub fn parse_path(&mut self) -> R<Path> {
        let start_span = self.lo_span();

        let mut segments = Vec::new();
        loop {
            let segment = self.parse_path_segment()?;
            segments.push(segment);
            if self.eat(Token::Dot) {
                continue;
            } else {
                break;
            }
        }

        let p = Path {
            segments,
            span: start_span.to(self.hi_span()),
        };

        Ok(p)
    }

    pub fn parse_path_segment(&mut self) -> R<PathSegment> {
        let lo = self.lo_span();
        let identifier = self.parse_identifier()?;
        let arguments = self.parse_optional_type_arguments()?;

        let segment = PathSegment {
            id: self.next_id(),
            identifier,
            arguments,
            span: lo.to(self.hi_span()),
        };

        Ok(segment)
    }

    pub fn parse_path_node(&mut self) -> R<PathNode> {
        Ok(PathNode {
            id: self.next_id(),
            path: self.parse_path()?,
        })
    }
}

impl Parser {
    /// Tries to convert a path-like expression into a Path.
    /// Returns Some(Path) if the expression can be converted, None otherwise.
    ///
    /// Path-like expressions are:
    /// - `ExpressionKind::Identifier` → single-segment path
    /// - `ExpressionKind::Member { target, name }` → recurse, append segment
    /// - `ExpressionKind::Specialize { target, type_arguments }` → recurse, add type args to last segment
    fn expr_to_path(&self, expr: &Expression) -> Option<Path> {
        match &expr.kind {
            ExpressionKind::Identifier(identifier) => {
                let segment = PathSegment {
                    id: expr.id,
                    identifier: identifier.clone(),
                    arguments: None,
                    span: expr.span,
                };
                Some(Path {
                    span: expr.span,
                    segments: vec![segment],
                })
            }
            ExpressionKind::Member { target, name } => {
                let mut path = self.expr_to_path(target)?;
                let segment = PathSegment {
                    id: self.next_index.borrow_mut().next(),
                    identifier: name.clone(),
                    arguments: None,
                    span: name.span,
                };
                path.segments.push(segment);
                path.span = path.span.to(name.span);
                Some(path)
            }
            ExpressionKind::Specialize {
                target,
                type_arguments,
            } => {
                let mut path = self.expr_to_path(target)?;
                // Add type arguments to the last segment
                if let Some(last) = path.segments.last_mut() {
                    last.arguments = Some(type_arguments.clone());
                    last.span = last.span.to(type_arguments.span);
                    path.span = path.span.to(type_arguments.span);
                }
                Some(path)
            }
            _ => None,
        }
    }

    fn try_parse_struct_literal(&mut self, expr: Box<Expression>) -> R<Box<Expression>> {
        if !self.matches(Token::LBrace) {
            return Ok(expr);
        }

        // Check if we're at a `{` and struct literals are allowed
        let struct_literals_allowed = !self.restrictions.contains(Restrictions::NO_STRUCT_LITERALS);

        if !struct_literals_allowed {
            // If it looks like a struct literal, we should report an error but still parse it
            // to avoid confusing "expected block" or "improper label" errors.
            if self.looks_like_struct_literal() {
                self.emit_error(ParserError::DisallowedStructLiteral, self.lo_span());
                // Fallthrough to parse it as struct literal (recovery)
            } else {
                // Not a struct literal context, return the expression as-is
                return Ok(expr);
            }
        }

        // Try to convert the expression to a path
        let Some(path) = self.expr_to_path(&expr) else {
            return Err(Spanned::new(ParserError::ExpectedPathExpression, expr.span));
        };

        // Parse the struct literal with the converted path
        let span = expr.span;
        self.parse_struct_literal(path, span)
    }

    fn looks_like_struct_literal(&mut self) -> bool {
        // pattern: { Key ...
        if !self.next_matches(
            1,
            Token::Identifier {
                value: String::new(),
            },
        ) {
            // Note: We can't easily match Identifier with content without complex logic,
            // but matches checks strict equality.
            // Token::Identifier usually carries data.
            // We need to check variant.
            if let Some(tok) = self.next(1) {
                if !matches!(tok, Token::Identifier { .. }) {
                    return false;
                }
            } else {
                return false;
            }
        } else {
            // next_matches expects exact match. Use manual check.
            // unreachable because we check below
        }

        // pattern: { Key, ...
        if self.next_matches(2, Token::Comma) {
            return true;
        }

        // pattern: { Key: ...
        if self.next_matches(2, Token::Colon) {
            // pattern: { Key: Val, ...
            // We can check lookahead 3 (Val) and 4 (Comma/RBrace)
            // But simpler: if we see colon, it's either Label or Struct Field.
            // If NO_STRUCT_LITERALS is on (e.g. if condition), Label is valid but weird (improper position).
            // Struct Field is invalid.
            // But detecting "Val, " strongly implies struct.

            // Check if next(4) is comma (Idx 0={ 1=Key 2=: 3=Val 4=, )
            if self.next_matches(4, Token::Comma) {
                return true;
            }

            // Check for Literals at 3?
            if let Some(tok) = self.next(3) {
                match tok {
                    Token::String { .. }
                    | Token::Integer { .. }
                    | Token::Float { .. }
                    | Token::True
                    | Token::False
                    | Token::Nil => {
                        // Likely struct: { x: 1 } or { x: 1, }
                        return true;
                    }
                    _ => {}
                }
            }
        }

        false
    }

    fn parse_struct_literal(&mut self, path: Path, span: Span) -> R<Box<Expression>> {
        let fields = self.parse_expression_field_list()?;
        let literal = StructLiteral { path, fields };
        let kind = ExpressionKind::StructLiteral(literal);
        let span = span.to(self.hi_span());
        Ok(self.build_expr(kind, span))
    }

    fn parse_expression_field_list(&mut self) -> R<Vec<ExpressionField>> {
        self.parse_delimiter_sequence(Delimiter::Brace, Token::Comma, |p| {
            p.parse_expression_field()
        })
    }

    fn parse_expression_field(&mut self) -> R<ExpressionField> {
        let lo = self.lo_span();
        let label = self.parse_label()?;

        let expr = self.parse_expression()?;
        let field = ExpressionField {
            is_shorthand: label.is_none(),
            label,
            expression: expr,
            span: lo.to(self.hi_span()),
        };

        Ok(field)
    }
}

impl Parser {
    #[allow(unused)]
    fn parse_operator_from_token(&mut self) -> R<OperatorKind> {
        let kind = match self.current_token() {
            Token::Plus => Some(OperatorKind::Add),
            Token::Minus => Some(OperatorKind::Sub),
            Token::Star => Some(OperatorKind::Mul),
            Token::Quotient => Some(OperatorKind::Div),
            Token::Modulus => Some(OperatorKind::Rem),

            Token::AmpAmp => Some(OperatorKind::BoolAnd),
            Token::BarBar => Some(OperatorKind::BoolOr),

            Token::Amp => Some(OperatorKind::BitAnd),
            Token::Bar => Some(OperatorKind::BitOr),
            Token::Caret => Some(OperatorKind::BitXor),

            Token::Shl => Some(OperatorKind::BitShl),
            Token::Shr => Some(OperatorKind::BitShr),

            Token::Eql => Some(OperatorKind::Eq),
            Token::Neq => Some(OperatorKind::Neq),
            Token::Geq => Some(OperatorKind::Geq),
            Token::Leq => Some(OperatorKind::Leq),

            Token::RChevron => Some(OperatorKind::Gt),
            Token::LChevron => Some(OperatorKind::Lt),

            Token::PlusEq => Some(OperatorKind::AddAssign),
            Token::MinusEq => Some(OperatorKind::SubAssign),
            Token::MulEq => Some(OperatorKind::MulAssign),
            Token::DivEq => Some(OperatorKind::DivAssign),
            Token::RemEq => Some(OperatorKind::RemAssign),

            Token::AmpEq => Some(OperatorKind::BitAndAssign),
            Token::BarEq => Some(OperatorKind::BitOrAssign),
            Token::CaretEq => Some(OperatorKind::BitXorAssign),

            Token::ShlEq => Some(OperatorKind::BitShlAssign),
            Token::ShrEq => Some(OperatorKind::BitShrAssign),
            Token::Bang => Some(OperatorKind::Not),
            _ => None,
        };

        if let Some(kind) = kind {
            self.bump();
            return Ok(kind);
        }

        if self.matches(Token::LBracket) && self.next_matches(1, Token::RBracket) {
            self.bump();
            self.bump();
            if self.eat(Token::Assign) {
                return Ok(OperatorKind::IndexAssign);
            }
            return Ok(OperatorKind::Index);
        }

        if self.matches(Token::Underscore) && self.next_matches(1, Token::Minus) {
            self.bump();
            self.bump();
            return Ok(OperatorKind::Neg);
        }

        Err(self.err_at_current(ParserError::UnknownOperator))
    }
}

impl Parser {
    fn bin_op_non_assign(k: Token) -> Option<BinaryOperator> {
        match k {
            Token::Plus => Some(BinaryOperator::Add),
            Token::Minus => Some(BinaryOperator::Sub),
            Token::Star => Some(BinaryOperator::Mul),
            Token::Quotient => Some(BinaryOperator::Div),
            Token::Modulus => Some(BinaryOperator::Rem),

            Token::AmpAmp => Some(BinaryOperator::BoolAnd),
            Token::BarBar => Some(BinaryOperator::BoolOr),

            Token::Amp => Some(BinaryOperator::BitAnd),
            Token::Bar => Some(BinaryOperator::BitOr),
            Token::Caret => Some(BinaryOperator::BitXor),

            Token::Shl => Some(BinaryOperator::BitShl),
            Token::Shr => Some(BinaryOperator::BitShr),

            Token::Eql => Some(BinaryOperator::Eql),
            Token::Neq => Some(BinaryOperator::Neq),
            Token::Geq => Some(BinaryOperator::Geq),
            Token::Leq => Some(BinaryOperator::Leq),

            Token::RChevron => Some(BinaryOperator::Gt),
            Token::LChevron => Some(BinaryOperator::Lt),
            Token::PtrEq => Some(BinaryOperator::PtrEq),
            _ => None,
        }
    }

    fn bin_op_assign(k: Token) -> Option<BinaryOperator> {
        match k {
            Token::PlusEq => Some(BinaryOperator::Add),
            Token::MinusEq => Some(BinaryOperator::Sub),
            Token::MulEq => Some(BinaryOperator::Mul),
            Token::DivEq => Some(BinaryOperator::Div),
            Token::RemEq => Some(BinaryOperator::Rem),

            Token::AmpEq => Some(BinaryOperator::BitAnd),
            Token::BarEq => Some(BinaryOperator::BitOr),
            Token::CaretEq => Some(BinaryOperator::BitXor),

            Token::ShlEq => Some(BinaryOperator::BitShl),
            Token::ShrEq => Some(BinaryOperator::BitShr),
            _ => None,
        }
    }
}

#[derive(Debug)]
enum ParserError {
    #[allow(unused)]
    Expected(Token, Token),
    ExpectedIdentifier,
    ExpectedSemiColon,
    ExpectedDeclaration,
    ExpectedTopLevelDeclaration,
    ExpectedType,
    ExpectedGenericRequirement,
    ExpectedMatchingPattern,
    ExpectedElseBlock,
    ExpectedExpression,
    InvalidCollectionType,
    TopLevelOperatorNotAllowed,
    RequiredIdentifierPattern,
    DissallowedAssociatedDeclaration,
    DissallowedFunctionDeclaration,
    DissallowedNamespaceDeclaration,
    DisallowedRestPatterns,
    DisallowedLocalBindingPattern,
    DisallowedWildcardExpression,
    DisallowedBindingCondition,
    DisallowedLabel,
    FunctionBodyRequired,
    UnknownBinaryOperator,
    UnknownOperator,
    ExpectedParameterNameOrLabel,
    ExpectedParameterName,
    ExpectedSelf,
    ExpectedExternAbiString,
    DissallowedExternDeclaration,
    ExternFunctionBodyNotAllowed,
    DisallowedStructLiteral,
    ExpectedPathExpression,
    ExtraTypeArguments,
    UnexpectedSemicolonInList {
        context: &'static str,
    },
}

impl Display for ParserError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use ParserError::*;
        match self {
            Expected(expected, found) => {
                // Using debug here so we don't require Token: Display
                write!(f, "expected token {:?}, found {:?}", expected, found)
            }
            ExpectedIdentifier => f.write_str("expected identifier"),
            ExpectedSemiColon => f.write_str("expected ';'"),
            ExpectedDeclaration => f.write_str("expected declaration"),
            ExpectedTopLevelDeclaration => f.write_str("expected top-level declaration"),
            ExpectedType => f.write_str("expected type"),
            ExpectedGenericRequirement => f.write_str("expected generic requirement"),
            ExpectedMatchingPattern => f.write_str("expected a matching pattern"),
            ExpectedElseBlock => f.write_str("expected 'else' block"),
            ExpectedExpression => f.write_str("expected expression"),
            InvalidCollectionType => f.write_str("invalid collection type"),
            TopLevelOperatorNotAllowed => f.write_str("top-level operator not allowed"),
            RequiredIdentifierPattern => f.write_str("identifier pattern required"),
            DissallowedAssociatedDeclaration => f.write_str("disallowed associated declaration"),
            DissallowedFunctionDeclaration => f.write_str("disallowed function declaration"),
            DissallowedNamespaceDeclaration => f.write_str("disallowed namespace declaration"),
            DisallowedRestPatterns => f.write_str("disallowed rest patterns"),
            DisallowedLocalBindingPattern => f.write_str("disallowed local binding pattern"),
            DisallowedWildcardExpression => f.write_str("disallowed wildcard expression"),
            DisallowedBindingCondition => f.write_str("disallowed binding condition"),
            DisallowedLabel => f.write_str("disallowed label"),
            FunctionBodyRequired => f.write_str("function body required"),
            UnknownBinaryOperator => f.write_str("unknown binary operator"),
            UnknownOperator => f.write_str("unknown operator"),
            ExpectedParameterNameOrLabel => f.write_str("expected parameter name or label"),
            ExpectedParameterName => f.write_str("expected parameter name"),
            ExpectedSelf => f.write_str("expected 'self'"),
            ExpectedExternAbiString => f.write_str("expected extern ABI string"),
            DissallowedExternDeclaration => f.write_str("disallowed extern declaration"),
            ExternFunctionBodyNotAllowed => f.write_str("extern functions cannot have a body"),
            DisallowedStructLiteral => {
                f.write_str("struct literals are not allowed in this context")
            }
            ExpectedPathExpression => f.write_str(
                "expected a path expression (identifier, member access, or type specialization)",
            ),
            ExtraTypeArguments => f.write_str("extra type arguments provided"),
            UnexpectedSemicolonInList { context } => {
                write!(f, "unexpected semicolon in {}", context)
            }
        }
    }
}
struct FnParseMode {
    req_body: bool,
}

enum Delimiter {
    /// `( ... )`
    Parenthesis,
    /// `{ ... }`
    Brace,
    /// `[ ... ]`
    Bracket,
    /// `| ... |`
    Bar,
}

impl Delimiter {
    fn open(&self) -> Token {
        match self {
            Delimiter::Parenthesis => Token::LParen,
            Delimiter::Brace => Token::LBrace,
            Delimiter::Bracket => Token::LBracket,
            Delimiter::Bar => Token::Bar,
        }
    }

    fn close(&self) -> Token {
        match self {
            Delimiter::Parenthesis => Token::RParen,
            Delimiter::Brace => Token::RBrace,
            Delimiter::Bracket => Token::RBracket,
            Delimiter::Bar => Token::Bar,
        }
    }
}

fn is_generic_type_disambiguating_token(token: Token) -> bool {
    use Token::*;

    if matches!(
        token,
        RParen
            | RBracket
            | LBrace
            | RBrace
            | Dot
            | Comma
            | Semicolon
            | EOF
            | QuestionDot
            | Bang
            | Colon
            | Question
            | Assign
            | As
            | RChevron
    ) {
        return true;
    }

    if matches!(token, LParen | LBracket) {
        return true;
    }

    return false;
}

bitflags::bitflags! {
    #[derive(Clone, Copy, Debug)]
    struct Restrictions: u8 {
        const ALLOW_BINDING_CONDITION = 1 << 0;
        const ALLOW_WILDCARD = 1 << 1;
        const ALLOW_REST_PATTERN = 1 << 2;
        const NO_STRUCT_LITERALS = 1 << 3;
    }
}

impl Parser {
    fn with_restrictions<T>(&mut self, res: Restrictions, f: impl FnOnce(&mut Self) -> T) -> T {
        let old = self.restrictions.clone();
        self.restrictions = res;
        let res = f(self);
        self.restrictions = old;
        res
    }
}
