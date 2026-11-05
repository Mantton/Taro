use crate::{
    ast::{
        self, AnonConst, AssociatedDeclaration, AssociatedDeclarationKind, Attribute, AttributeArg,
        AttributeArgs, AttributeList, BinaryOperator, Block, CfgExpr, ClosureExpression,
        ComputedProperty, ConformanceConstraint, Conformances, Constant, ConstructorPath,
        Declaration, DeclarationKind, Enum, EnumCase, Expression, ExpressionArgument,
        ExpressionField, ExpressionKind, FieldDefinition, ForStatement, Function,
        FunctionDeclaration, FunctionParameter, FunctionPrototype, FunctionSignature, GenericBound,
        GenericBounds, GenericRequirement, GenericRequirementList, GenericWhereClause, Generics,
        Identifier, IfExpression, Impl, Interface, Label, Literal, Local, MapPair, MatchArm,
        MatchExpression, ModuleDecl, Mutability, Namespace, NamespaceDeclaration,
        NamespaceDeclarationKind, NodeID, Path, PathNode, PathSegment, Pattern,
        PatternBindingCondition, PatternKind, RequiredTypeConstraint, Statement, StatementKind,
        StaticVariable, Struct, StructLiteral, Type, TypeAlias, TypeArgument, TypeArguments,
        TypeKind, TypeParameter, TypeParameterKind, TypeParameters, UnaryOperator, UseTree,
        UseTreeKind, UseTreeNestedItem, UseTreePath, Variant, VariantKind, Visibility,
        VisibilityLevel,
    },
    diagnostics::DiagCtx,
    error::ReportedError,
    parse::{Base, lexer, token::Token},
    span::{Position, Span, Spanned, Symbol},
};
use std::{cell::RefCell, fmt::Display, rc::Rc};

type NextNode = Rc<RefCell<NodeTagger>>;
#[derive(Debug, Default)]
struct NodeTagger {
    next_index: u32,
    #[cfg(test)]
    allocations: usize,
}
impl NodeTagger {
    fn next(&mut self) -> NodeID {
        let id = NodeID::from_raw(self.next_index);
        self.next_index += 1;
        #[cfg(test)]
        {
            self.allocations += 1;
        }
        id
    }
}
pub fn parse_package(
    package: lexer::Pacakge,
    dcx: &DiagCtx,
) -> Result<ast::Package, ReportedError> {
    let next: NextNode = Default::default();
    let root = parse_module(package.root, next, dcx, true)?;
    Ok(ast::Package { root })
}

fn parse_module(
    module: lexer::Module,
    next: NextNode,
    dcx: &DiagCtx,
    is_root: bool,
) -> Result<ast::Module, ReportedError> {
    let name = Symbol::new(&module.name);
    let mut files = vec![];
    let mut submodules = vec![];
    let mut module_decls: Vec<ModuleDecl> = vec![];

    for file in module.files {
        let (file, decls) = parse_file(file, next.clone(), dcx)?;
        files.push(file);
        module_decls.extend(decls);
    }

    for module in module.submodules {
        let module = parse_module(module, next.clone(), dcx, false)?;
        submodules.push(module);
    }

    let module_decl =
        pick_module_decl(&module.name, is_root, module_decls, dcx).map_err(|_| ReportedError)?;

    Ok(ast::Module {
        id: next.borrow_mut().next(),
        name,
        files,
        submodules,
        module_decl,
    })
}

fn pick_module_decl(
    module_name: &str,
    is_root: bool,
    mut decls: Vec<ModuleDecl>,
    dcx: &DiagCtx,
) -> Result<Option<ModuleDecl>, ReportedError> {
    if decls.is_empty() {
        return Ok(None);
    }

    let mut had_error = false;

    if is_root {
        for decl in &decls {
            dcx.emit_error(ParserError::ModuleDeclInRoot.to_string(), Some(decl.span));
            had_error = true;
        }
        if had_error {
            return Err(ReportedError);
        }
        return Ok(None);
    }

    let first = decls.remove(0);
    for extra in &decls {
        dcx.emit_error(
            ParserError::DuplicateModuleDecl.to_string(),
            Some(extra.span),
        );
        had_error = true;
    }

    let declared = first.name.symbol.as_str().to_string();
    if declared != module_name {
        dcx.emit_error(
            ParserError::ModuleDeclNameMismatch {
                declared,
                expected: module_name.to_string(),
            }
            .to_string(),
            Some(first.name.span),
        );
        had_error = true;
    }

    if had_error {
        return Err(ReportedError);
    }

    Ok(Some(first))
}

fn parse_file(
    file: lexer::File,
    next: NextNode,
    dcx: &DiagCtx,
) -> Result<(ast::File, Vec<ModuleDecl>), ReportedError> {
    let id = file.id;
    let parser = Parser::new(file, next.clone());
    let (declarations, module_decls, warnings) = match parser.parse() {
        Ok(items) => items,
        Err((errors, warnings)) => {
            for warning in warnings {
                dcx.emit_warning(warning.value.to_string(), Some(warning.span));
            }
            for err in errors {
                dcx.emit_error(err.value.to_string(), Some(err.span));
            }
            return Err(ReportedError);
        }
    };
    for warning in warnings {
        dcx.emit_warning(warning.value.to_string(), Some(warning.span));
    }

    Ok((ast::File { id, declarations }, module_decls))
}

type R<V> = Result<V, Spanned<ParserError>>;
mod subscript;
#[derive(Clone, Copy)]
struct ParserCheckpoint {
    cursor: usize,
    token_splits: usize,
    errors: usize,
    warnings: usize,
    next_node: u32,
}

struct Parser {
    file: lexer::File,
    cursor: usize,
    restrictions: Restrictions,
    token_splits: Vec<(usize, Spanned<Token>)>,
    next_index: NextNode,
    errors: Vec<Spanned<ParserError>>,
    warnings: Vec<Spanned<ParserError>>,
}

impl Parser {
    fn new(file: lexer::File, next: NextNode) -> Parser {
        Parser {
            file,
            cursor: 0,
            restrictions: Restrictions::empty(),
            token_splits: Vec::new(),
            errors: vec![],
            warnings: vec![],
            next_index: next,
        }
    }
}

impl Parser {
    fn parse(
        mut self,
    ) -> Result<
        (Vec<Declaration>, Vec<ModuleDecl>, Vec<Spanned<ParserError>>),
        (Vec<Spanned<ParserError>>, Vec<Spanned<ParserError>>),
    > {
        let result = self.parse_module_declarations();
        match result {
            Ok(_) if !self.errors.is_empty() => Err((self.errors, self.warnings)),
            Ok((declarations, module_decls)) => Ok((declarations, module_decls, self.warnings)),
            Err(error) => {
                self.errors.push(error);
                Err((self.errors, self.warnings))
            }
        }
    }
}

impl Parser {
    #[inline]
    fn token_kind_eq(lhs: &Token, rhs: &Token) -> bool {
        std::mem::discriminant(lhs) == std::mem::discriminant(rhs)
    }

    fn current(&self) -> Option<&Spanned<Token>> {
        if self.cursor >= self.file.tokens.len() {
            return None;
        }
        Some(&self.file.tokens[self.cursor])
    }

    fn previous(&self) -> Option<&Spanned<Token>> {
        if self.cursor == 0 {
            return self.current();
        }
        if self.cursor - 1 >= self.file.tokens.len() {
            return None;
        }
        Some(&self.file.tokens[self.cursor - 1])
    }

    fn current_token(&self) -> &Token {
        static EOF_TOKEN: Token = Token::EOF;
        if let Some(token) = self.current() {
            return &token.value;
        }
        &EOF_TOKEN
    }

    fn is_at_end(&self) -> bool {
        self.cursor >= self.file.tokens.len() - 1
    }

    fn bump(&mut self) {
        self.cursor += 1;
    }

    fn checkpoint(&self) -> ParserCheckpoint {
        ParserCheckpoint {
            cursor: self.cursor,
            token_splits: self.token_splits.len(),
            errors: self.errors.len(),
            warnings: self.warnings.len(),
            next_node: self.next_index.borrow().next_index,
        }
    }

    /// Speculation must restore token edits and diagnostics as well as the cursor.
    fn restore(&mut self, checkpoint: ParserCheckpoint) {
        for (index, original) in self.token_splits.drain(checkpoint.token_splits..).rev() {
            self.file.tokens.remove(index + 1);
            self.file.tokens[index] = original;
        }
        self.cursor = checkpoint.cursor;
        self.errors.truncate(checkpoint.errors);
        self.warnings.truncate(checkpoint.warnings);
        self.next_index.borrow_mut().next_index = checkpoint.next_node;
    }

    fn matches(&self, token: Token) -> bool {
        Self::token_kind_eq(self.current_token(), &token)
    }

    fn matches_any(&self, tokens: &[Token]) -> bool {
        let current = self.current_token();
        for token in tokens {
            if Self::token_kind_eq(current, token) {
                return true;
            }
        }
        return false;
    }

    fn matches_question(&self) -> bool {
        matches!(
            self.current_token(),
            &Token::Question | &Token::QuestionQuestion
        )
    }

    fn split_token(&mut self, token: Token) {
        let original = self.file.tokens[self.cursor].clone();
        let span = original.span;
        let mid = Position {
            line: span.start.line,
            offset: span.start.offset + 1,
        };
        self.token_splits.push((self.cursor, original));
        self.file.tokens[self.cursor] = Spanned::new(token.clone(), Span { end: mid, ..span });
        self.file.tokens.insert(
            self.cursor + 1,
            Spanned::new(token, Span { start: mid, ..span }),
        );
    }

    fn eat_question(&mut self) -> bool {
        match self.current_token() {
            &Token::Question => {
                self.bump();
                true
            }
            &Token::QuestionQuestion => {
                self.split_token(Token::Question);
                self.bump();
                true
            }
            _ => false,
        }
    }

    fn eat_amp(&mut self) -> bool {
        match self.current_token() {
            &Token::Amp => {
                self.bump();
                true
            }
            &Token::AmpAmp => {
                self.split_token(Token::Amp);
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
                self.current_token().clone(),
            )))
        }
    }

    fn expect_amp(&mut self) -> R<()> {
        if self.eat_amp() {
            Ok(())
        } else {
            Err(self.err_at_current(ParserError::Expected(
                Token::Amp,
                self.current_token().clone(),
            )))
        }
    }

    fn eat(&mut self, token: Token) -> bool {
        if Self::token_kind_eq(self.current_token(), &token) {
            self.bump();
            return true;
        }

        false
    }

    fn next(&self, index: usize) -> Option<&Token> {
        let k = self.cursor + index;
        if k >= self.file.tokens.len() {
            return None;
        }

        Some(&self.file.tokens[k].value)
    }

    fn next_matches(&self, index: usize, token: Token) -> bool {
        let Some(tok) = self.next(index) else {
            return false;
        };

        Self::token_kind_eq(tok, &token)
    }
    fn expect(&mut self, token: Token) -> R<()> {
        if Self::token_kind_eq(self.current_token(), &token) {
            self.bump();
            Ok(())
        } else {
            Err(self.err_at_current(ParserError::Expected(token, self.current_token().clone())))
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
    fn intern_symbol(&self, text: &str) -> Symbol {
        Symbol::new(text)
    }

    fn symbol_eq(&self, symbol: impl AsRef<str>, text: &str) -> bool {
        symbol.as_ref() == text
    }

    fn next_id(&mut self) -> NodeID {
        self.next_index.borrow_mut().next()
    }
}

impl Parser {
    fn emit_warning(&mut self, err: ParserError, span: Span) {
        self.warnings.push(Spanned::new(err, span));
    }
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
    fn synchronize_declaration(&mut self) {
        while !self.is_at_end() {
            if self.eat(Token::Semicolon) {
                return;
            }

            if let Some(token) = self.current() {
                match token.value {
                    Token::Function
                    | Token::Struct
                    | Token::Class
                    | Token::Final
                    | Token::Enum
                    | Token::Interface
                    | Token::Namespace
                    | Token::Impl
                    | Token::Extend
                    | Token::Conform
                    | Token::Export
                    | Token::Import
                    | Token::Type
                    | Token::Const
                    | Token::At => return,
                    _ => {
                        self.bump();
                    }
                }
            } else {
                break;
            }
        }
    }

    fn synchronize_statement(&mut self) {
        let mut braces = 0usize;
        while !self.is_at_end() {
            match self.current_token() {
                Token::LBrace => {
                    braces += 1;
                    self.bump();
                }
                Token::RBrace if braces != 0 => {
                    braces -= 1;
                    self.bump();
                }
                Token::RBrace => return,
                Token::Semicolon if braces == 0 => {
                    self.bump();
                    return;
                }
                Token::Let
                | Token::Var
                | Token::If
                | Token::Return
                | Token::For
                | Token::While
                | Token::Defer
                | Token::Guard
                | Token::Match
                    if braces == 0 =>
                {
                    return;
                }
                _ => {
                    self.bump();
                }
            }
        }
    }

    fn parse_module_declarations(&mut self) -> R<(Vec<Declaration>, Vec<ModuleDecl>)> {
        let mut items = vec![];
        let mut module_decls = vec![];
        loop {
            if self.is_at_end() {
                break;
            }
            match self.parse_top_level_item() {
                Ok(Some(TopLevelItem::Decl(d))) => items.push(d),
                Ok(Some(TopLevelItem::Module(m))) => module_decls.push(m),
                Ok(None) => {
                    // No declaration matched, but we might not be at EOF if there are trailing invalid tokens
                    if !self.is_at_end() {
                        let err = self.err_at_current(ParserError::ExpectedTopLevelDeclaration);
                        self.emit_error(err.value, err.span);
                        self.bump(); // forcefully consume token to avoid infinite loop
                        self.synchronize_declaration();
                    } else {
                        break;
                    }
                }
                Err(e) => {
                    self.emit_error(e.value, e.span);
                    self.synchronize_declaration();
                }
            }
        }

        return Ok((items, module_decls));
    }

    fn parse_top_level_item(&mut self) -> R<Option<TopLevelItem>> {
        let (start_span, attributes, visibility) = self.parse_declaration_header()?;

        if self.matches(Token::Mod) {
            self.expect(Token::Mod)?;
            let name = self.parse_identifier()?;
            let span = start_span.to(self.hi_span());
            self.expect_semi()?;
            return Ok(Some(TopLevelItem::Module(ModuleDecl {
                name,
                visibility,
                attributes,
                span,
            })));
        }

        Ok(self
            .parse_declaration_body(
                start_span,
                attributes,
                visibility,
                FnParseMode { req_body: true },
            )?
            .map(TopLevelItem::Decl))
    }

    fn parse_declaration_header(&mut self) -> R<(Span, AttributeList, Visibility)> {
        let start = self.lo_span();
        let attributes = self.parse_attributes()?;
        let visibility = self.parse_visibility()?;
        Ok((start, attributes, visibility))
    }

    fn parse_declaration_internal(&mut self, fn_mode: FnParseMode) -> R<Option<Declaration>> {
        let (start, attributes, visibility) = self.parse_declaration_header()?;
        self.parse_declaration_body(start, attributes, visibility, fn_mode)
    }

    fn parse_declaration_body(
        &mut self,
        start_span: Span,
        attributes: AttributeList,
        visibility: Visibility,
        fn_mode: FnParseMode,
    ) -> R<Option<Declaration>> {
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

    fn convert_declaration<K: TryFrom<DeclarationKind>>(
        &mut self,
        declaration: Declaration,
        error: ParserError,
    ) -> Option<Declaration<K>> {
        let Declaration {
            id,
            span,
            identifier,
            kind,
            visibility,
            attributes,
        } = declaration;
        match K::try_from(kind) {
            Ok(kind) => Some(Declaration {
                id,
                span,
                identifier,
                kind,
                visibility,
                attributes,
            }),
            Err(_) => {
                self.emit_error(error, span);
                None
            }
        }
    }

    fn parse_declaration_list<T, I: IntoIterator<Item = T>>(
        &mut self,
        mut action: impl FnMut(&mut Parser) -> R<I>,
    ) -> R<Vec<T>> {
        self.expect(Token::LBrace)?;
        let mut decls = vec![];
        while !self.matches(Token::RBrace) && !self.is_at_end() {
            while self.eat(Token::Semicolon) {}
            if self.matches(Token::RBrace) {
                break;
            }
            let reported = self.errors.len();
            let mut parsed = action(self)?.into_iter().peekable();
            // A removed declaration form reports its own error and yields nothing.
            if parsed.peek().is_none() && self.errors.len() == reported {
                return Err(self.err_at_current(ParserError::ExpectedDeclaration));
            }
            decls.extend(parsed);
        }
        self.expect(Token::RBrace)?;
        Ok(decls)
    }
}

impl Parser {
    fn parse_associated_declaration(
        &mut self,
        fn_mode: FnParseMode,
    ) -> R<Vec<AssociatedDeclaration>> {
        let (start_span, attributes, visibility) = self.parse_declaration_header()?;
        if self.matches(Token::Var) {
            let declarations = self.parse_computed_property_associated(
                start_span,
                attributes,
                visibility,
                fn_mode.req_body,
            )?;
            self.eat(Token::Semicolon);
            return Ok(declarations);
        }
        let mut is_final = false;
        let mut is_override = false;
        let mut is_required = false;
        let mut is_convenience = false;
        while self.matches(Token::Final)
            || self.matches(Token::Override)
            || self.matches_contextual_identifier("required")
            || self.matches_contextual_identifier("convenience")
        {
            let modifier = self.current_token().clone();
            let span = self.lo_span();
            self.bump();
            let flag = if modifier == Token::Final {
                &mut is_final
            } else if modifier == Token::Override {
                &mut is_override
            } else if matches!(&modifier, Token::Identifier { value } if value == "required") {
                &mut is_required
            } else {
                &mut is_convenience
            };
            if *flag {
                self.emit_error(ParserError::DuplicateMethodModifier, span);
            }
            *flag = true;
        }
        if self.matches(Token::Deinit) {
            // The collector reclaims memory; explicit close() releases resources.
            // Skip the old body so one diagnostic covers the declaration.
            let span = self.lo_span();
            self.emit_error(ParserError::DeinitRemoved, span);
            self.bump();
            if self.matches(Token::LBrace) {
                self.parse_block()?;
            }
            self.eat(Token::Semicolon);
            return Ok(vec![]);
        }
        if self.matches(Token::Init) {
            if !fn_mode.req_body {
                return Err(self.err_at_current(ParserError::LifecycleRequiresExtension));
            }
            if is_final {
                return Err(self.err_at_current(ParserError::InvalidLifecycleModifier));
            }
            return self.parse_lifecycle_declaration(
                start_span,
                attributes,
                visibility,
                is_override,
                is_required,
                is_convenience,
            );
        }
        if is_required || is_convenience {
            return Err(self.err_at_current(ParserError::InvalidLifecycleModifier));
        }
        if self.matches_contextual_identifier("subscript") {
            return self.parse_native_subscript(
                start_span,
                attributes,
                visibility,
                fn_mode.req_body,
                is_final,
                is_override,
            );
        }
        // Associated instance methods have an implicit Self value. The extension
        // target decides whether Self is a value, storage reference, or class.
        let is_static = self.matches(Token::Static)
            && (self.next_matches(1, Token::Function) || self.next_matches(1, Token::Unsafe));
        if is_static {
            self.bump();
        }
        if (is_final || is_override)
            && (!self.matches(Token::Function) && !self.matches(Token::Unsafe) || is_static)
        {
            return Err(self.err_at_current(ParserError::InvalidMethodModifier));
        }
        let mut declaration =
            self.parse_declaration_body(start_span, attributes, visibility, fn_mode)?;
        if let Some(declaration) = &mut declaration {
            if let DeclarationKind::Function(function) = &mut declaration.kind {
                function.is_final = is_final;
                function.is_override = is_override;
                let receiver = function
                    .signature
                    .prototype
                    .inputs
                    .iter()
                    .find(|parameter| self.symbol_eq(parameter.name.symbol, "self"));
                if is_static {
                    if let Some(receiver) = receiver {
                        self.emit_error(ParserError::StaticFunctionHasReceiver, receiver.span);
                    }
                } else if receiver.is_none() {
                    let span = declaration.identifier.span;
                    let self_type = Type {
                        id: self.next_id(),
                        span,
                        kind: TypeKind::ImplicitSelf,
                    };
                    let receiver = FunctionParameter {
                        id: self.next_id(),
                        attributes: vec![],
                        label: None,
                        name: Identifier {
                            symbol: self.intern_symbol("self"),
                            span,
                        },
                        annotated_type: Box::new(self_type),
                        default_value: None,
                        is_variadic: false,
                        span,
                    };
                    function.signature.prototype.inputs.insert(0, receiver);
                }
            }
        }
        Ok(declaration
            .and_then(|decl| {
                self.convert_declaration(decl, ParserError::DissallowedAssociatedDeclaration)
            })
            .into_iter()
            .collect())
    }

    fn parse_lifecycle_declaration(
        &mut self,
        start: Span,
        attributes: AttributeList,
        visibility: Visibility,
        is_override: bool,
        is_required: bool,
        is_convenience: bool,
    ) -> R<Vec<AssociatedDeclaration>> {
        let keyword_span = self.lo_span();
        self.expect(Token::Init)?;
        // Construction is package-visible unless explicitly exported. Other
        // associated declarations keep their existing visibility defaults.
        let visibility = if visibility.level == ast::VisibilityLevel::Inherent {
            ast::Visibility {
                level: ast::VisibilityLevel::Internal,
                ..visibility
            }
        } else {
            visibility
        };
        let kind = {
            let mut function = self.parse_fn(FnParseMode { req_body: true }, false)?;
            if function.is_async {
                self.emit_error(
                    ParserError::InvalidInitializerSignature,
                    function.signature.span,
                );
            }
            for parameter in &function.signature.prototype.inputs {
                if self.symbol_eq(parameter.name.symbol, "self") {
                    self.emit_error(ParserError::InitializerReceiver, parameter.span);
                }
            }
            function.is_override = is_override;
            // Private, initially uninitialized storage, never a caller receiver.
            // Ordinary init uses result storage directly; fallible init keeps
            // this storage separate from its returned Result.
            let self_name = Identifier {
                symbol: self.intern_symbol("self"),
                span: keyword_span,
            };
            let self_local = Local {
                id: self.next_id(),
                mutability: Mutability::Mutable,
                pattern: Pattern {
                    id: self.next_id(),
                    span: keyword_span,
                    kind: PatternKind::Identifier(self_name),
                },
                ty: Some(Box::new(Type {
                    id: self.next_id(),
                    span: keyword_span,
                    kind: TypeKind::ImplicitSelf,
                })),
                initializer: None,
                is_shorthand: false,
            };
            let self_stmt = Statement {
                id: self.next_id(),
                span: keyword_span,
                kind: StatementKind::Variable(self_local),
            };
            function
                .block
                .as_mut()
                .expect("initializer body")
                .statements
                .insert(0, self_stmt);
            if function.signature.prototype.output.is_none() {
                function.signature.prototype.output = Some(Box::new(Type {
                    id: self.next_id(),
                    span: keyword_span,
                    kind: TypeKind::ImplicitSelf,
                }));
            }
            AssociatedDeclarationKind::Initializer(ast::Initializer {
                function,
                is_required,
                is_convenience,
            })
        };
        let span = start.to(self.hi_span());
        // Like method declarations, a braced lifecycle body is complete
        // without a trailing semicolon, including before the extension's `}`.
        self.eat(Token::Semicolon);
        Ok(vec![Declaration {
            id: self.next_id(),
            kind,
            span,
            visibility,
            attributes,
            identifier: Identifier {
                symbol: self.intern_symbol("init"),
                span: keyword_span,
            },
        }])
    }

    fn implicit_self_parameter(&mut self, span: Span) -> FunctionParameter {
        FunctionParameter {
            id: self.next_id(),
            attributes: vec![],
            label: None,
            name: Identifier {
                symbol: self.intern_symbol("self"),
                span,
            },
            annotated_type: Box::new(Type {
                id: self.next_id(),
                span,
                kind: TypeKind::ImplicitSelf,
            }),
            default_value: None,
            is_variadic: false,
            span,
        }
    }

    fn parse_computed_property_associated(
        &mut self,
        start: Span,
        attributes: AttributeList,
        visibility: Visibility,
        body_required: bool,
    ) -> R<Vec<AssociatedDeclaration>> {
        self.expect(Token::Var)?;
        let identifier = self.parse_identifier()?;
        self.expect(Token::Colon)?;
        let ty = self.parse_type()?;
        self.expect(Token::LBrace)?;
        let mut getter = None;
        let reported = self.errors.len();
        while !self.matches(Token::RBrace) && !self.is_at_end() {
            while self.eat(Token::Semicolon) {}
            if self.matches(Token::RBrace) {
                break;
            }
            if !self.matches_contextual_identifier("get") {
                self.emit_error(
                    ParserError::ExpectedComputedPropertyAccessor,
                    self.lo_span(),
                );
                self.discard_computed_property_accessors();
                break;
            }
            if getter.is_some() {
                self.emit_error(
                    ParserError::DuplicateComputedPropertyAccessor,
                    self.lo_span(),
                );
                self.discard_computed_property_accessors();
                break;
            }
            let accessor = self.parse_identifier()?;
            if matches!(
                self.current_token(),
                Token::LParen | Token::Async | Token::RArrow
            ) {
                self.emit_error(
                    ParserError::ComputedPropertyAccessorSignatureRemoved,
                    accessor.span,
                );
                self.discard_computed_property_accessors();
                break;
            }
            let block = if self.matches(Token::LBrace) {
                Some(self.parse_block()?)
            } else if body_required {
                self.emit_error(ParserError::FunctionBodyRequired, self.lo_span());
                self.discard_computed_property_accessors();
                break;
            } else {
                None
            };
            let receiver = self.implicit_self_parameter(accessor.span);
            getter = Some(Declaration {
                id: self.next_id(),
                span: accessor.span.to(self.hi_span()),
                identifier: self.make_hidden_property_accessor_identifier(&identifier),
                visibility,
                attributes: vec![],
                kind: AssociatedDeclarationKind::Function(Function {
                    generics: Generics {
                        type_parameters: None,
                        where_clause: None,
                    },
                    signature: FunctionSignature {
                        span: accessor.span,
                        prototype: FunctionPrototype {
                            inputs: vec![receiver],
                            output: None,
                        },
                    },
                    block,
                    is_unsafe: false,
                    is_async: false,
                    is_final: false,
                    is_override: false,
                    abi: None,
                }),
            });
        }
        self.expect(Token::RBrace)?;
        if self.errors.len() != reported {
            return Ok(vec![]);
        }
        let Some(getter) = getter else {
            self.emit_error(ParserError::MissingComputedPropertyGetter, identifier.span);
            return Ok(vec![]);
        };
        let declaration = Declaration {
            id: self.next_id(),
            span: start.to(self.hi_span()),
            identifier,
            visibility,
            attributes,
            kind: AssociatedDeclarationKind::Property(ComputedProperty {
                ty,
                getter_id: getter.id,
            }),
        };
        Ok(vec![declaration, getter])
    }

    /// Error recovery only: discard an unsupported accessor's token tree while
    /// leaving the property's closing brace for its declaration parser.
    fn discard_computed_property_accessors(&mut self) {
        let mut depth = 0usize;
        while !self.is_at_end() {
            match self.current_token() {
                Token::LBrace => depth += 1,
                Token::RBrace if depth == 0 => break,
                Token::RBrace => depth -= 1,
                _ => {}
            }
            self.bump();
        }
    }

    fn matches_contextual_identifier(&self, text: &str) -> bool {
        match self.current_token() {
            Token::Identifier { value } => value == text,
            _ => false,
        }
    }

    fn make_hidden_property_accessor_identifier(&mut self, property: &Identifier) -> Identifier {
        Identifier {
            symbol: self.intern_symbol(&format!("__prop_get_{}", property.symbol.as_str())),
            span: property.span,
        }
    }

    fn parse_function_declaration(&mut self) -> R<Option<FunctionDeclaration>> {
        let declaration = self.parse_declaration_internal(FnParseMode { req_body: true })?;
        Ok(declaration.and_then(|decl| {
            self.convert_declaration(decl, ParserError::DissallowedFunctionDeclaration)
        }))
    }

    fn parse_namespace_declaration(&mut self) -> R<Option<NamespaceDeclaration>> {
        let declaration = self.parse_declaration_internal(FnParseMode { req_body: true })?;
        Ok(declaration.and_then(|decl| {
            self.convert_declaration(decl, ParserError::DissallowedNamespaceDeclaration)
        }))
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
            Token::Class | Token::Final => self.parse_class_declaration()?,
            Token::Enum => self.parse_enum_declaration()?,
            Token::Interface => self.parse_interface()?,
            Token::Var | Token::Let => {
                return Err(self.err_at_current(ParserError::TopLevelVariableMustBeStatic));
            }
            Token::Identifier { .. } if self.next_matches(1, Token::ColonEq) => {
                return Err(self.err_at_current(ParserError::TopLevelVariableMustBeStatic));
            }
            Token::Static => self.parse_static_variable_decl()?,
            Token::Const => self.parse_const_decl()?,
            Token::Import => (
                Identifier::emtpy(self.file.id),
                self.parse_import_export_declaration(true)?,
            ),
            Token::Export => (
                Identifier::emtpy(self.file.id),
                self.parse_import_export_declaration(false)?,
            ),
            Token::Extern => self.parse_extern_declaration()?,
            Token::Type => self.parse_type_declaration()?,
            Token::Function | Token::Unsafe => self.parse_function_declaration_kind(mode)?,
            Token::Extend | Token::Conform | Token::Impl => {
                (Identifier::emtpy(self.file.id), self.parse_impl()?)
            }
            Token::Namespace => self.parse_namespace()?,

            _ => return Ok(None),
        };

        Ok(Some((identifier, kind)))
    }
}

impl Parser {
    fn parse_function_declaration_kind(
        &mut self,
        mode: FnParseMode,
    ) -> R<(Identifier, DeclarationKind)> {
        let is_unsafe = self.eat(Token::Unsafe);
        if is_unsafe && !self.matches(Token::Function) {
            return Err(self.err_at_current(ParserError::UnsafeModifierRequiresFunction));
        }

        self.parse_function(mode, is_unsafe)
    }

    fn parse_extern_declaration(&mut self) -> R<(Identifier, DeclarationKind)> {
        self.expect(Token::Extern)?;
        let abi = match self.current_token() {
            Token::String { value } => {
                let abi = self.intern_symbol(value);
                self.bump();
                abi
            }
            _ => return Err(self.err_at_current(ParserError::ExpectedExternAbiString)),
        };

        if self.matches(Token::LBrace) {
            let declarations: Vec<Declaration<ast::ExternDeclarationKind>> =
                self.parse_declaration_list(|p| p.parse_extern_block_declaration(abi))?;
            return Ok((
                Identifier::emtpy(self.file.id),
                DeclarationKind::ExternBlock(ast::ExternBlock { abi, declarations }),
            ));
        }

        if self.matches(Token::Function) || self.matches(Token::Unsafe) {
            let (identifier, mut kind) =
                self.parse_function_declaration_kind(FnParseMode { req_body: false })?;
            let DeclarationKind::Function(func) = &mut kind else {
                return Ok((identifier, kind));
            };

            if let Some(block) = &func.block {
                self.emit_error(ParserError::ExternFunctionBodyNotAllowed, block.span);
                func.block = None;
            }
            func.abi = Some(abi);

            return Ok((identifier, kind));
        }

        Err(self.err_at_current(ParserError::ExpectedExternDeclaration))
    }

    fn parse_extern_block_declaration(
        &mut self,
        _abi: Symbol,
    ) -> R<Option<Declaration<ast::ExternDeclarationKind>>> {
        // Handle opaque type declarations: `type Identifier`
        if self.eat(Token::Type) {
            let start = self.previous().unwrap().span;
            let identifier = self.parse_identifier()?;
            let span = start.to(identifier.span);
            return Ok(Some(Declaration {
                id: self.next_id(),
                span,
                identifier,
                kind: ast::ExternDeclarationKind::Type(ast::OpaqueType),
                visibility: ast::Visibility {
                    span,
                    level: ast::VisibilityLevel::Private,
                },
                attributes: vec![],
            }));
        }

        let declaration = self.parse_declaration_internal(FnParseMode { req_body: false })?;
        let Some(mut declaration) = declaration.and_then(|decl| {
            self.convert_declaration::<ast::ExternDeclarationKind>(
                decl,
                ParserError::DissallowedExternDeclaration,
            )
        }) else {
            return Ok(None);
        };
        if let ast::ExternDeclarationKind::Function(func) = &mut declaration.kind {
            if func.block.is_some() {
                self.emit_error(ParserError::ExternFunctionBodyNotAllowed, declaration.span);
                func.block = None;
            }
            func.abi = Some(_abi);
        }
        Ok(Some(declaration))
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
            self.emit_error(
                ParserError::QualifiedPathSeparator,
                self.previous().unwrap().span,
            );
            UseTreeKind::Glob
        } else if self.eat_path_separator() {
            if self.eat(Token::Star) {
                UseTreeKind::Glob
            } else {
                self.parse_use_tree_nested()?
            }
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
            let is_coupler = ((self.matches(Token::ColonColon) || self.matches(Token::Dot))
                && (self.next_matches(1, Token::LBrace) || self.next_matches(1, Token::Star)))
                || self.matches(Token::DotStar);

            if is_coupler || !self.eat_path_separator() {
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
    fn parse_static_variable_decl(&mut self) -> R<(Identifier, DeclarationKind)> {
        self.expect(Token::Static)?;
        if self.matches(Token::Let) {
            self.emit_error(ParserError::LetRemoved(None), self.lo_span());
            self.bump();
        } else if !self.eat(Token::Var) {
            return Err(self.err_at_current(ParserError::ExpectedStaticVar));
        }
        let mutability = Mutability::Mutable;

        let identifier = self.parse_identifier()?;
        if !self.eat(Token::Colon) {
            return Err(Spanned::new(
                ParserError::MissingStaticTypeAnnotation,
                identifier.span,
            ));
        }
        let ty = self.parse_type()?;

        if !self.eat(Token::Assign) {
            return Err(Spanned::new(
                ParserError::MissingStaticInitializer,
                identifier.span,
            ));
        }
        let initializer = self.parse_expression()?;

        let decl = StaticVariable {
            identifier,
            mutability,
            ty,
            initializer,
        };

        Ok((identifier, DeclarationKind::StaticVariable(decl)))
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

        let (ty, interface_set) = if self.eat(Token::Assign) {
            let first = self.parse_type()?;
            if self.eat(Token::Amp) {
                let Type {
                    id,
                    kind: TypeKind::Nominal(path),
                    ..
                } = *first
                else {
                    return Err(self.err_at_current(ParserError::ExpectedInterfaceSetMember));
                };

                let mut bounds = vec![GenericBound {
                    path: PathNode { id, path },
                }];
                loop {
                    bounds.extend(self.parse_generic_bound()?);
                    if !self.eat(Token::Amp) {
                        break;
                    }
                }
                (None, Some(bounds))
            } else {
                (Some(first), None)
            }
        } else {
            (None, None)
        };

        let where_clause = self.parse_generic_where_clause()?;

        let generics = Generics {
            type_parameters,
            where_clause,
        };

        let decl = TypeAlias {
            ty,
            interface_set,
            generics,
            bounds,
        };

        let k = DeclarationKind::TypeAlias(decl);
        Ok((identifier, k))
    }
}

impl Parser {
    /// Parse `extend T` or `conform T to I`, preserving the common semantic
    /// implementation node. Legacy impl syntax is recovered only for a targeted
    /// error; it never produces an accepted source file.
    fn parse_impl(&mut self) -> R<DeclarationKind> {
        let legacy = self.matches(Token::Impl);
        let conformance = self.matches(Token::Conform);
        let keyword_span = self.lo_span();
        self.bump();
        if legacy {
            self.emit_error(ParserError::LegacyImplDeclaration, keyword_span);
        }
        let type_parameters = self.parse_type_parameters()?;

        let first_type = self.parse_type()?;

        let (interface, target) = if conformance {
            if !self.matches_contextual_identifier("to") {
                return Err(self.err_at_current(ParserError::ExpectedConformanceTo));
            }
            self.bump();
            let interface = self.parse_type()?;
            (Some(interface), first_type)
        } else if legacy && self.eat(Token::For) {
            let target = self.parse_type()?;
            (Some(first_type), target)
        } else {
            (None, first_type)
        };

        let where_clause = self.parse_generic_where_clause()?;

        let declarations = self.parse_declaration_list(|p| {
            p.parse_associated_declaration(FnParseMode { req_body: true })
        })?;
        if interface.is_some() {
            for declaration in &declarations {
                if matches!(declaration.kind, AssociatedDeclarationKind::Initializer(_)) {
                    self.emit_error(
                        ParserError::LifecycleRequiresExtension,
                        declaration.identifier.span,
                    );
                }
            }
        }

        let generics = Generics {
            type_parameters,
            where_clause,
        };

        let impl_block = Impl {
            generics,
            interface,
            target,
            declarations,
        };

        Ok(DeclarationKind::Impl(impl_block))
    }
}

impl Parser {
    fn parse_struct_declaration(&mut self) -> R<(Identifier, DeclarationKind)> {
        self.expect(Token::Struct)?;
        let identifier = self.parse_identifier()?;
        let type_parameters = self.parse_type_parameters()?;
        let conformances = self.parse_conformances()?;
        let where_clause = self.parse_generic_where_clause()?;
        let generics = Generics {
            type_parameters,
            where_clause,
        };

        let fields = self.parse_field_definitions(Delimiter::Brace)?;

        let s = Struct {
            generics,
            fields,
            conformances,
        };
        let s = DeclarationKind::Struct(s);
        Ok((identifier, s))
    }

    fn parse_class_declaration(&mut self) -> R<(Identifier, DeclarationKind)> {
        let is_final = self.eat(Token::Final);
        self.expect(Token::Class)?;
        let identifier = self.parse_identifier()?;
        let type_parameters = self.parse_type_parameters()?;
        let conformances = self.parse_conformances()?;
        let where_clause = self.parse_generic_where_clause()?;
        let fields = self.parse_field_definitions(Delimiter::Brace)?;
        Ok((
            identifier,
            DeclarationKind::Class(ast::Class {
                generics: Generics {
                    type_parameters,
                    where_clause,
                },
                fields,
                conformances,
                is_final,
            }),
        ))
    }

    fn parse_enum_declaration(&mut self) -> R<(Identifier, DeclarationKind)> {
        self.expect(Token::Enum)?;
        let identifier = self.parse_identifier()?;
        let type_parameters = self.parse_type_parameters()?;
        let conformances = self.parse_conformances()?;
        let where_clause = self.parse_generic_where_clause()?;
        let generics = Generics {
            type_parameters,
            where_clause,
        };

        let cases = self.parse_delimiter_sequence(Delimiter::Brace, Token::Semicolon, |this| {
            this.parse_enum_case()
        })?;
        let e = Enum {
            generics,
            cases,
            conformances,
        };
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
        let span = self.lo_span();
        match self.current_token() {
            Token::Identifier { value: symbol } => {
                let v = Identifier {
                    span,
                    symbol: self.intern_symbol(symbol),
                };
                self.bump();
                if matches!(
                    v.symbol.as_str(),
                    "FnMut" | "FnOnce" | "AsyncFnMut" | "AsyncFnOnce"
                ) {
                    self.emit_error(ParserError::RemovedCallableKind(v.symbol), span);
                }
                return Ok(v);
            }
            _ => {
                return Err(self.err_at_current(ParserError::ExpectedIdentifier));
            }
        };
    }

    fn parse_member_identifier(&mut self) -> R<Identifier> {
        let span = self.lo_span();
        match self.current_token() {
            Token::Identifier { value: symbol } => {
                let v = Identifier {
                    span,
                    symbol: self.intern_symbol(symbol),
                };
                self.bump();
                Ok(v)
            }
            Token::Init => {
                let v = Identifier {
                    span,
                    symbol: self.intern_symbol("init"),
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

    fn parse_reference_modifier(&mut self) {
        let error = if self.eat(Token::Const) {
            Some(ParserError::ReferenceConstModifier)
        } else if self.eat(Token::Mut) {
            Some(ParserError::MutableReferenceRemoved)
        } else {
            None
        };
        if let Some(error) = error {
            self.emit_error(error, self.previous().unwrap().span);
        }
    }

    fn parse_pointer_mutability(&mut self) -> Mutability {
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

            // When attributes are stacked on separate lines, ASI inserts a
            // semicolon between them (e.g. `@test\n@ignore\nfunc foo()`).
            // Speculatively eat any trailing semicolons; if the next real token
            // isn't another `@`, restore so the semicolon is still available for
            // the caller (e.g. `expect_semi` in `parse_declaration_internal`).
            if self.matches(Token::Semicolon) {
                let cp = self.checkpoint();
                while self.eat(Token::Semicolon) {}
                if !self.matches(Token::At) {
                    self.restore(cp);
                    break;
                }
                // Another `@attr` follows — let the loop parse it.
            }
        }

        self.eat(Token::Semicolon);
        Ok(attrs)
    }

    fn parse_attribute(&mut self) -> R<Option<Attribute>> {
        let lo = self.lo_span();
        if !self.eat(Token::At) {
            return Ok(None);
        };

        if self.matches(Token::Unsafe) {
            return Err(self.err_at_current(ParserError::UnsafeAttributeRemoved));
        }

        let identifier = self.parse_identifier()?;

        // Parse attribute arguments. `@cfg(...)` supports both:
        // - predicate syntax: `@cfg(os("macos"))`
        // - legacy key/value syntax: `@cfg(target_os = "macos")`
        let mut cfg_expr = None;
        let args = if self.matches(Token::LParen) {
            if self.symbol_eq(identifier.symbol, "cfg") {
                let checkpoint = self.checkpoint();
                self.bump(); // consume `(`
                let parsed_cfg = self.parse_cfg_expr().and_then(|expr| {
                    self.expect(Token::RParen)?;
                    Ok(expr)
                });

                match parsed_cfg {
                    Ok(expr) => {
                        cfg_expr = Some(expr);
                        None
                    }
                    Err(_) => {
                        self.restore(checkpoint);
                        Some(self.parse_attribute_args()?)
                    }
                }
            } else {
                Some(self.parse_attribute_args()?)
            }
        } else {
            None
        };

        let attr = Attribute {
            identifier,
            args,
            cfg_expr,
            span: lo.to(self.hi_span()),
        };
        return Ok(Some(attr));
    }

    fn parse_attribute_args(&mut self) -> R<AttributeArgs> {
        let lo = self.lo_span();
        let items =
            self.parse_delimiter_sequence(Delimiter::Parenthesis, Token::Comma, |this| {
                this.parse_attribute_arg()
            })?;

        Ok(AttributeArgs {
            items,
            span: lo.to(self.hi_span()),
        })
    }

    fn parse_attribute_arg(&mut self) -> R<AttributeArg> {
        let lo = self.lo_span();
        if Self::is_attribute_literal_token(self.current_token()) {
            let value = self.parse_attribute_literal_value()?;
            return Ok(AttributeArg::Literal {
                value,
                span: lo.to(self.hi_span()),
            });
        }

        let key = self.parse_identifier()?;
        if self.eat(Token::Assign) {
            // key = value
            let value = self.parse_attribute_literal_value()?;
            return Ok(AttributeArg::KeyValue {
                key,
                value,
                span: lo.to(self.hi_span()),
            });
        }

        // flag
        Ok(AttributeArg::Flag {
            key,
            span: lo.to(self.hi_span()),
        })
    }

    /// Parse a literal value for use in attributes (returns ast::Literal directly)
    fn parse_attribute_literal_value(&mut self) -> R<Literal> {
        let literal = match self.current_token() {
            Token::Integer {
                value,
                base,
                suffix,
            } => Literal::Integer {
                value: value.clone(),
                base: *base,
                suffix: *suffix,
            },
            Token::Float { value, .. } => Literal::Float {
                value: value.clone(),
            },
            Token::String { value } => Literal::String {
                value: value.clone(),
            },
            Token::Rune { value } => Literal::Rune {
                value: value.clone(),
            },
            Token::True => Literal::Bool(true),
            Token::False => Literal::Bool(false),
            Token::Nil => Literal::Nil,
            _ => return Err(self.err_at_current(ParserError::ExpectedExpression)),
        };

        self.bump(); // consume token
        Ok(literal)
    }

    fn is_attribute_literal_token(token: &Token) -> bool {
        matches!(
            token,
            Token::Integer { .. }
                | Token::Float { .. }
                | Token::String { .. }
                | Token::Rune { .. }
                | Token::True
                | Token::False
                | Token::Nil
        )
    }

    /// Parse `#cfg(...)` compile-time configuration check expression
    fn parse_cfg_check_expression(&mut self) -> R<Box<Expression>> {
        let lo = self.lo_span();
        self.expect(Token::Hash)?;

        // Expect "cfg" identifier
        let ident = self.parse_identifier()?;
        if !self.symbol_eq(ident.symbol, "cfg") {
            return Err(Spanned::new(ParserError::ExpectedCfgIdentifier, ident.span));
        }

        self.expect(Token::LParen)?;
        let cfg_expr = self.parse_cfg_expr()?;
        self.expect(Token::RParen)?;

        let kind = ExpressionKind::CfgCheck(cfg_expr);
        Ok(self.build_expr(kind, lo.to(self.hi_span())))
    }

    /// Parse a cfg expression: `bench && !os("windows")`.
    fn parse_cfg_expr(&mut self) -> R<CfgExpr> {
        self.parse_cfg_or_expr()
    }

    /// Parse OR expressions: `expr || expr`
    fn parse_cfg_or_expr(&mut self) -> R<CfgExpr> {
        let lo = self.lo_span();
        let mut left = self.parse_cfg_and_expr()?;

        while self.eat(Token::BarBar) {
            let right = self.parse_cfg_and_expr()?;
            // Flatten consecutive ORs into a single Any
            match &mut left {
                CfgExpr::Any(items, span) => {
                    items.push(right);
                    *span = lo.to(self.hi_span());
                }
                _ => {
                    left = CfgExpr::Any(vec![left, right], lo.to(self.hi_span()));
                }
            }
        }

        Ok(left)
    }

    /// Parse AND expressions: `expr && expr`
    fn parse_cfg_and_expr(&mut self) -> R<CfgExpr> {
        let lo = self.lo_span();
        let mut left = self.parse_cfg_unary_expr()?;

        while self.eat(Token::AmpAmp) {
            let right = self.parse_cfg_unary_expr()?;
            // Flatten consecutive ANDs into a single All
            match &mut left {
                CfgExpr::All(items, span) => {
                    items.push(right);
                    *span = lo.to(self.hi_span());
                }
                _ => {
                    left = CfgExpr::All(vec![left, right], lo.to(self.hi_span()));
                }
            }
        }

        Ok(left)
    }

    /// Parse unary: `!expr` or primary
    fn parse_cfg_unary_expr(&mut self) -> R<CfgExpr> {
        let lo = self.lo_span();
        if self.eat(Token::Bang) {
            let inner = self.parse_cfg_unary_expr()?;
            Ok(CfgExpr::Not(Box::new(inner), lo.to(self.hi_span())))
        } else {
            self.parse_cfg_primary_expr()
        }
    }

    /// Parse primary cfg expression: `os("macos")` or `(expr)`
    fn parse_cfg_primary_expr(&mut self) -> R<CfgExpr> {
        if self.eat(Token::LParen) {
            let inner = self.parse_cfg_expr()?;
            self.expect(Token::RParen)?;
            return Ok(inner);
        }

        // Parse a boolean flag (`bench`) or a valued predicate
        // (`os("macos")`). Flags are needed by both `@cfg(bench)` and
        // expression-form `#cfg(bench)`.
        let lo = self.lo_span();
        let name = self.parse_identifier()?;
        if !self.matches(Token::LParen) {
            return Ok(CfgExpr::Flag {
                name,
                span: lo.to(self.hi_span()),
            });
        }
        self.expect(Token::LParen)?;

        // Parse string value
        let value = match self.current_token() {
            Token::String { value } => {
                let value = self.intern_symbol(value);
                self.bump();
                value
            }
            _ => return Err(self.err_at_current(ParserError::ExpectedExpression)),
        };

        self.expect(Token::RParen)?;

        Ok(CfgExpr::Predicate {
            name,
            value,
            span: lo.to(self.hi_span()),
        })
    }
}

impl Parser {
    fn parse_visibility(&mut self) -> R<Visibility> {
        let lo = self.lo_span();
        let level = if self.eat(Token::Public) {
            VisibilityLevel::Public
        } else if self.eat(Token::Private) {
            VisibilityLevel::Private
        } else if self.eat(Token::Internal) {
            VisibilityLevel::Internal
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
        // `weak` remains a valid field/module name when followed by `:`.
        if self.matches_contextual_identifier("weak") && !self.next_matches(1, Token::Colon) {
            let span = self.lo_span();
            self.emit_error(ParserError::WeakStorageRemoved, span);
            self.bump();
        }

        let mutability = if self.eat(Token::Readonly) {
            Mutability::Immutable
        } else {
            Mutability::Mutable
        };

        let identifier = self.parse_identifier()?;
        self.expect(Token::Colon)?;

        let ty = self.parse_type()?;
        let default_value = if self.eat(Token::Assign) {
            Some(self.parse_expression()?)
        } else {
            None
        };
        let fd = FieldDefinition {
            id: self.next_id(),
            default_value,
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
        self.expect(delim.open())?;
        let mut fields = Vec::new();
        while !self.matches(delim.close()) {
            fields.push(self.parse_field_definition()?);
            if self.eat(Token::Comma) {
                self.eat(Token::Semicolon);
            } else if !self.eat(Token::Semicolon) {
                break;
            }
        }
        self.expect(delim.close())?;
        Ok(fields)
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
            Token::LBrace => self.parse_struct_variant(),
            _ => Ok(VariantKind::Unit),
        }
    }

    fn parse_struct_variant(&mut self) -> R<VariantKind> {
        self.expect(Token::LBrace)?;
        let mut fields = vec![];
        let mut names = std::collections::HashSet::new();
        while self.eat(Token::Semicolon) {}
        while !self.matches(Token::RBrace) && !self.is_at_end() {
            let mut field = self.parse_field_definition()?;
            self.check_enum_payload_visibility(&field.visibility);
            if !names.insert(field.identifier.symbol) {
                self.emit_error(
                    ParserError::DuplicateEnumPayloadField(field.identifier.symbol),
                    field.identifier.span,
                );
            }
            field.label = Some(Label {
                identifier: field.identifier,
                span: field.identifier.span,
            });
            fields.push(field);
            if self.matches(Token::RBrace) {
                break;
            }
            if !(self.eat(Token::Comma) || self.eat(Token::Semicolon)) {
                return Err(self.err_at_current(ParserError::ExpectedEnumPayloadSeparator));
            }
            while self.eat(Token::Semicolon) {}
        }
        self.expect(Token::RBrace)?;
        Ok(VariantKind::Struct(fields))
    }

    fn parse_tuple_variant(&mut self) -> R<VariantKind> {
        let fields = self.parse_delimiter_sequence(Delimiter::Parenthesis, Token::Comma, |p| {
            p.parse_tuple_variant_field()
        })?;

        let k = VariantKind::Tuple(fields);
        Ok(k)
    }

    /// A payload is exposed through its variant; field-level visibility would
    /// otherwise be parsed and silently discarded by constructor collection.
    fn check_enum_payload_visibility(&mut self, visibility: &Visibility) {
        if visibility.level != VisibilityLevel::Inherent {
            self.emit_error(ParserError::EnumPayloadVisibility, visibility.span);
        }
    }

    fn parse_tuple_variant_field(&mut self) -> R<FieldDefinition> {
        let lo = self.lo_span();
        let vis = self.parse_visibility()?;
        self.check_enum_payload_visibility(&vis);

        let mutability = if self.eat(Token::Readonly) {
            Mutability::Immutable
        } else {
            Mutability::Mutable
        };

        let label = self.parse_label()?;
        let ty = self.parse_type()?;

        let def = FieldDefinition {
            id: self.next_id(),
            default_value: None,
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
            Token::Identifier { .. } if self.matches_contextual_identifier("some") => {
                self.bump();
                let interfaces = self.parse_sequence(Token::Amp, |this| this.parse_path_node())?;
                Ok(TypeKind::ImplTrait { interfaces })
            }
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
            Token::Bang => {
                self.bump();
                Ok(TypeKind::Never)
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
        let mutability = if is_pointer {
            self.parse_pointer_mutability()
        } else {
            {
                self.parse_reference_modifier();
                Mutability::Immutable
            }
        };
        let ty = self.parse_type()?;

        let kind = if is_pointer {
            TypeKind::Pointer(ty, mutability)
        } else {
            TypeKind::Reference(ty)
        };

        Ok(kind)
    }

    fn parse_tuple_type(&mut self) -> R<TypeKind> {
        self.expect(Token::LParen)?;
        let (elements, trailing) = if self.eat(Token::RParen) {
            (Vec::new(), false)
        } else {
            let first = self.parse_type()?;
            if self.eat(Token::As) {
                let interface = self.parse_type()?;
                self.expect(Token::RParen)?;
                self.expect(Token::Dot)?;
                let member = self.parse_identifier()?;
                return Ok(TypeKind::QualifiedAccess {
                    target: first,
                    interface,
                    member,
                });
            }
            self.parse_delimiter_sequence_tail(Delimiter::Parenthesis, Token::Comma, first, |p| {
                p.parse_type()
            })?
        };

        if self.matches(Token::RArrow) {
            self.expect(Token::RArrow)?;
            let output = self.parse_type()?;

            let kind = TypeKind::Function {
                inputs: elements,
                output,
            };

            return Ok(kind);
        }

        if elements.len() == 1 && !trailing {
            let first = elements.into_iter().next().unwrap();
            return Ok(TypeKind::Parenthesis(first));
        }

        Ok(TypeKind::Tuple(elements))
    }

    fn parse_collection_type(&mut self) -> R<TypeKind> {
        // Parses [T], [T; N], [T; ..], and [T: V].
        // eat opening bracket
        self.expect(Token::LBracket)?;
        let ty = self.parse_type()?;

        let kind = if self.eat(Token::RBracket) {
            return Ok(TypeKind::List(ty));
        } else if self.eat(Token::Colon) {
            let value = self.parse_type()?;
            TypeKind::Dictionary { key: ty, value }
        } else if self.eat(Token::Semicolon) {
            if self.eat(Token::DotDot) {
                TypeKind::Slice(ty)
            } else {
                let len = self.parse_anon_const()?;
                TypeKind::Array {
                    size: len,
                    element: ty,
                }
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
    /// Parse the shared bracket grammar without guessing from a following `(`.
    /// Failed lookahead restores diagnostics and split tokens. When both parses
    /// survive, reserve the first parse's IDs before constructing the second.
    fn parse_bracket_suffix(
        &mut self,
    ) -> R<(Option<TypeArguments>, Option<Vec<ExpressionArgument>>)> {
        let start = self.checkpoint();
        let type_parse = self.parse_type_arguments();
        let type_end = self.cursor;
        let type_nodes = self.next_index.borrow().next_index;
        let type_ok = type_parse.is_ok() && self.errors.len() == start.errors;
        self.restore(start);
        if type_ok {
            self.next_index.borrow_mut().next_index = type_nodes;
        }
        let expression_parse = self.parse_expression_argument_list(Delimiter::Bracket);
        if let Ok(index) = expression_parse {
            if !type_ok {
                return Ok((None, Some(index)));
            }
            if self.cursor == type_end && self.errors.len() == start.errors {
                return Ok((Some(type_parse.unwrap()), Some(index)));
            }
        }
        self.restore(start);
        // Reparse the selected grammar so token splits and IDs agree with the
        // retained tree, even when the speculative expression consumed farther.
        self.parse_type_arguments()
            .map(|arguments| (Some(arguments), None))
    }

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
            Token::Identifier { .. } if self.next_matches(1, Token::Assign) => {
                let identifier = self.parse_identifier()?;
                self.expect(Token::Assign)?;
                let ty = self.parse_type()?;
                Ok(TypeArgument::AssocType(identifier, ty))
            }
            _ => {
                let ty = self.parse_type()?;
                Ok(TypeArgument::Type(ty))
            }
        }
    }

    fn parse_optional_type_arguments(&mut self) -> R<Option<TypeArguments>> {
        if !self.matches(Token::LBracket) {
            return Ok(None);
        }
        let checkpoint = self.checkpoint();
        if let Ok(arguments) = self.parse_type_arguments() {
            if is_generic_type_disambiguating_token(self.current_token()) {
                return Ok(Some(arguments));
            }
        }
        self.restore(checkpoint);
        Ok(None)
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
        Ok(bounds.into_iter().flatten().collect())
    }

    /// A removed `!Bound` relaxation is reported and dropped.
    fn parse_generic_bound(&mut self) -> R<Option<GenericBound>> {
        let lo = self.lo_span();
        let relaxed = self.eat(Token::Bang);
        let path = self.parse_path_node()?;
        if relaxed {
            self.emit_error(ParserError::RelaxedBoundRemoved, lo.to(self.hi_span()));
            return Ok(None);
        }
        Ok(Some(GenericBound { path }))
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
    fn parse_conformances(&mut self) -> R<Option<Conformances>> {
        if self.eat(Token::Colon) {
            let lo = self.lo_span();
            let entries = self.parse_sequence(Token::Comma, |this| this.parse_generic_bound())?;
            let node = Conformances {
                bounds: entries
                    .into_iter()
                    .flatten()
                    .map(|bound| bound.path)
                    .collect(),
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
            Token::Amp | Token::AmpAmp => self.reject_reference_pattern(),
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
            Token::Dot | Token::Identifier { .. } => self.parse_constructor_path_kind(),
            _ => {
                // A pattern literal may have a unary minus, but `|` separates
                // alternatives here rather than forming a bitwise expression.
                let ac = AnonConst {
                    value: self.parse_prefix_expr()?,
                };
                Ok(PatternKind::Literal(ac))
            }
        }
    }

    fn parse_pattern_tuple_kind(&mut self) -> R<PatternKind> {
        let lo = self.lo_span();
        let mut res = Restrictions::empty();
        res.insert(Restrictions::ALLOW_REST_PATTERN);
        let (mut pats, trailing) = self.with_restrictions(res, |p| {
            p.parse_delimiter_sequence_trailing(Delimiter::Parenthesis, Token::Comma, |p| {
                p.parse_pattern()
            })
        })?;
        // `(pat)` without a trailing comma is a parenthesized pattern;
        // `(pat,)` is a one-element tuple pattern. Empty `()` stays a tuple.
        if pats.len() == 1 && !trailing {
            return Ok(pats.remove(0).kind);
        }
        Ok(PatternKind::Tuple(pats, lo.to(self.hi_span())))
    }

    fn reject_reference_pattern(&mut self) -> R<PatternKind> {
        let span = self.lo_span();
        self.expect_amp()?;
        self.emit_error(ParserError::ReferencePatternRemoved, span);
        self.parse_reference_modifier();
        Ok(self.parse_pattern()?.kind)
    }

    fn parse_constructor_path_kind(&mut self) -> R<PatternKind> {
        // Cannot Possibly be a path pattern
        if matches!(self.current_token(), Token::Identifier { .. })
            && !(self.next_matches(1, Token::ColonColon)
                || self.next_matches(1, Token::Dot)
                || self.next_matches(1, Token::LParen)
                || self.next_matches(1, Token::LBrace)
                || self.next_matches(1, Token::LBracket))
        {
            let ident = self.parse_identifier()?;
            return Ok(PatternKind::Identifier(ident));
        }

        let path = self.parse_constructor_path()?;

        match self.current_token() {
            Token::LBrace => {
                let lo = self.lo_span();
                let mut rest = false;
                let mut names = std::collections::HashSet::new();
                let fields = self
                    .parse_delimiter_sequence(Delimiter::Brace, Token::Comma, |p| {
                        if p.eat(Token::DotDot) {
                            if rest {
                                p.emit_error(ParserError::InvalidNamedPatternRest, p.hi_span());
                            }
                            rest = true;
                            return Ok(None);
                        }
                        if rest {
                            p.emit_error(ParserError::InvalidNamedPatternRest, p.lo_span());
                        }
                        let name = p.parse_identifier()?;
                        if !names.insert(name.symbol) {
                            p.emit_error(ParserError::DuplicateNamedField(name.symbol), name.span);
                        }
                        let pattern = if p.eat(Token::Colon) {
                            p.parse_pattern()?
                        } else {
                            Pattern {
                                id: p.next_id(),
                                span: name.span,
                                kind: PatternKind::Identifier(name),
                            }
                        };
                        Ok(Some(ast::NamedPatternField { name, pattern }))
                    })?
                    .into_iter()
                    .flatten()
                    .collect();
                Ok(PatternKind::PathNamed {
                    path,
                    fields,
                    rest,
                    field_span: lo.to(self.hi_span()),
                })
            }
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
    //   .Case         => ConstructorPathHead::Inferred
    //   A(::B)*       => ConstructorPathHead::Qualified
    pub fn parse_constructor_path(&mut self) -> R<ConstructorPath> {
        // Shorthand: `.Case`
        let lo = self.lo_span();
        if self.eat(Token::Dot) {
            let name = self.parse_identifier()?;
            let span = lo.to(self.hi_span());
            return Ok(ConstructorPath::Inferred { name, span });
        }

        // Full: A(::B)*
        let path = self.parse_path()?;
        Ok(ConstructorPath::Qualified { path })
    }
}

// Block
impl Parser {
    fn parse_block(&mut self) -> R<Block> {
        let lo = self.lo_span();
        let mut has_declarations = false;
        let statements = self.with_restrictions(
            self.restrictions
                - (Restrictions::NO_STRUCT_LITERALS
                    | Restrictions::ALLOW_BINDING_CONDITION
                    | Restrictions::STOP_CONDITION_CONNECTORS),
            |p| {
                p.parse_block_sequence(|p| {
                    let s = p.parse_statement()?;
                    has_declarations =
                        has_declarations || matches!(s.kind, StatementKind::Declaration(..));
                    Ok(s)
                })
            },
        )?;

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
        // A label followed by `name :=` would otherwise silently parse a
        // mistyped `value: Type := initializer` as a different variable.
        if label.is_some()
            && matches!(self.current_token(), Token::Identifier { .. })
            && self.next_matches(1, Token::ColonEq)
        {
            return Err(self.err_at_current(ParserError::TypedShorthandDeclaration));
        }
        match self.current_token() {
            Token::Loop | Token::While | Token::For => {}
            _ => self.warn_improper_label_position(label),
        };

        match self.current_token() {
            Token::Let | Token::Var => self.parse_local_statement(),
            Token::Identifier { value }
                if value == "weak"
                    && (self.next_matches(1, Token::Var) || self.next_matches(1, Token::Let)) =>
            {
                self.parse_local_statement()
            }
            Token::Identifier { .. } if self.next_matches(1, Token::ColonEq) => {
                self.parse_shorthand_local_statement()
            }
            Token::Loop => self.parse_loop_stmt(label),
            Token::While => self.parse_while_stmt(label),
            Token::For => self.parse_for_stmt(label),
            Token::Defer => self.parse_defer_stmt(),
            Token::Guard => self.parse_guard_stmt(),
            _ => {
                // `unsafe { ... }` is an expression statement, not a declaration start.
                let can_start_decl =
                    !self.matches(Token::Unsafe) || self.next_matches(1, Token::Function);
                if can_start_decl {
                    if let Some(decl) = self.parse_function_declaration()? {
                        return Ok(StatementKind::Declaration(decl));
                    }
                }

                let expr = self.parse_expression()?;
                return Ok(StatementKind::Expression(expr));
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
        // var <binding_pattern> <type_annotation>? <initializer_clause>?
        // type_annotation = : <type>
        // initializer_clause: = <expr>
        if self.matches_contextual_identifier("weak") {
            let span = self.lo_span();
            self.emit_error(ParserError::WeakStorageRemoved, span);
            self.bump();
        }
        let removed_let = self.matches(Token::Let).then(|| self.lo_span());
        if removed_let.is_none() {
            self.expect(Token::Var)?;
        } else {
            self.bump();
        }

        let pattern = self.parse_pattern()?;
        if !matches!(
            pattern.kind,
            PatternKind::Identifier(..)
                | PatternKind::Wildcard
                | PatternKind::Tuple(..)
                | PatternKind::PathNamed { .. }
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

        if let Some(span) = removed_let {
            // Suggest the shorthand only where it can replace the declaration.
            let shorthand = match (&pattern.kind, &ty, &initializer) {
                (PatternKind::Identifier(name), None, Some(_)) => Some(name.symbol),
                _ => None,
            };
            self.emit_error(ParserError::LetRemoved(shorthand), span);
        }

        let local = Local {
            id: self.next_id(),
            mutability: Mutability::Mutable,
            pattern,
            ty,
            initializer,
            is_shorthand: false,
        };

        Ok(local)
    }
    fn parse_shorthand_local_statement(&mut self) -> R<StatementKind> {
        let identifier = self.parse_identifier()?;
        self.expect(Token::ColonEq)?;
        let initializer = self.parse_expression()?;
        let pattern = Pattern {
            id: self.next_id(),
            span: identifier.span,
            kind: PatternKind::Identifier(identifier),
        };
        Ok(StatementKind::Variable(Local {
            id: self.next_id(),
            mutability: Mutability::Mutable,
            pattern,
            ty: None,
            initializer: Some(initializer),
            is_shorthand: true,
        }))
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
        let condition = self.parse_condition()?;
        let block = self.parse_block()?;

        Ok(StatementKind::While {
            label,
            condition,
            block,
        })
    }

    fn parse_for_stmt(&mut self, label: Option<Label>) -> R<StatementKind> {
        self.expect(Token::For)?;
        let is_await = self.eat(Token::Await);
        let pattern = self.parse_pattern()?;
        self.expect(Token::In)?;

        let for_restrictions = Restrictions::NO_STRUCT_LITERALS;

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
            is_await,
            pattern,
            iterator,
            clause,
            block,
        };
        Ok(StatementKind::For(f))
    }
}

impl Parser {
    fn parse_return_expression(&mut self) -> R<Box<Expression>> {
        let lo = self.lo_span();
        self.expect(Token::Return)?;

        if self.matches_any(&[Token::Semicolon, Token::RBrace]) {
            let kind = ExpressionKind::Return { value: None };
            return Ok(self.build_expr(kind, lo.to(self.hi_span())));
        }

        let value = Some(self.parse_expression()?);
        let kind = ExpressionKind::Return { value };
        Ok(self.build_expr(kind, lo.to(self.hi_span())))
    }

    fn parse_break_expression(&mut self) -> R<Box<Expression>> {
        let lo = self.lo_span();
        self.expect(Token::Break)?;
        let label = self.parse_optional_identifier()?;
        let kind = ExpressionKind::Break { label };
        Ok(self.build_expr(kind, lo.to(self.hi_span())))
    }

    fn parse_continue_expression(&mut self) -> R<Box<Expression>> {
        let lo = self.lo_span();
        self.expect(Token::Continue)?;
        let label = self.parse_optional_identifier()?;
        let kind = ExpressionKind::Continue { label };
        Ok(self.build_expr(kind, lo.to(self.hi_span())))
    }

    fn parse_defer_stmt(&mut self) -> R<StatementKind> {
        self.expect(Token::Defer)?;
        let block = if self.matches(Token::LBrace) {
            self.parse_block()?
        } else {
            // Exactly `defer { expression }`: capture/evaluation timing and
            // cleanup control-flow rules remain owned by ordinary block lowering.
            let expression = self.parse_expression()?;
            let span = expression.span;
            Block {
                id: self.next_id(),
                statements: vec![Statement {
                    id: self.next_id(),
                    kind: StatementKind::Expression(expression),
                    span,
                }],
                span,
                has_declarations: false,
            }
        };
        Ok(StatementKind::Defer(block))
    }

    fn parse_guard_stmt(&mut self) -> R<StatementKind> {
        self.expect(Token::Guard)?;

        let condition = self.parse_condition()?;

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
        action: F,
    ) -> R<Vec<T>>
    where
        F: FnMut(&mut Parser) -> R<T>,
    {
        let (items, _) = self.parse_delimiter_sequence_trailing(delim, separator, action)?;
        Ok(items)
    }

    /// Like `parse_delimiter_sequence`, but also reports whether a trailing
    /// separator was consumed after the last item. Used by tuple parsing to
    /// distinguish `(x)` (parenthesized) from `(x,)` (one-element tuple).
    fn parse_delimiter_sequence_trailing<T, F>(
        &mut self,
        delim: Delimiter,
        separator: Token,
        mut action: F,
    ) -> R<(Vec<T>, bool)>
    where
        F: FnMut(&mut Parser) -> R<T>,
    {
        // eat open
        self.expect(delim.open())?;

        // if immediately closed return empty vec
        if self.eat(delim.close()) {
            return Ok((Vec::new(), false));
        }

        let first = action(self)?;
        self.parse_delimiter_sequence_tail(delim, separator, first, action)
    }

    fn parse_delimiter_sequence_tail<T>(
        &mut self,
        delim: Delimiter,
        separator: Token,
        first: T,
        mut action: impl FnMut(&mut Parser) -> R<T>,
    ) -> R<(Vec<T>, bool)> {
        let mut items = vec![first];
        let mut trailing = false;
        while self.eat(separator.clone()) {
            if self.matches(delim.close()) {
                trailing = true;
                break;
            }
            items.push(action(self)?);
        }

        if self.matches(Token::Semicolon) {
            return Err(self.err_at_current(ParserError::UnexpectedSemicolonInList {
                context: "multiline list - add a trailing comma before the newline",
            }));
        }

        self.expect(delim.close())?;
        Ok((items, trailing))
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
            let start = self.cursor;
            match parse_action(self) {
                Ok(item) => items.push(item),
                Err(e) => {
                    self.emit_error(e.value, e.span);
                    self.synchronize_statement();
                    // A recognized restart token can itself be invalid in this
                    // context. Never retry it indefinitely without consuming it.
                    if self.cursor == start && !self.matches(Token::RBrace) && !self.is_at_end() {
                        self.bump();
                    }
                }
            }

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
        // Nested grouped/call expressions have their normal operator grammar.
        // A binding initializer opts into the connector boundary explicitly.
        let expression = self.with_restrictions(
            self.restrictions - Restrictions::STOP_CONDITION_CONNECTORS,
            Self::parse_assignment_expr,
        )?;
        if self.matches(Token::ColonEq)
            && self
                .restrictions
                .contains(Restrictions::ALLOW_BINDING_CONDITION)
        {
            return Err(self.err_at_current(ParserError::ConditionalShorthandBinding));
        }
        Ok(expression)
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
        // Right-associative: use recursion instead of loop
        // This makes `a ?? b ?? c` parse as `a ?? (b ?? c)`
        if self.eat(Token::QuestionQuestion) {
            // Recursively parse the rest (right-associative)
            let right = self.parse_optional_default_expr()?;

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

        while !self
            .restrictions
            .contains(Restrictions::STOP_CONDITION_CONNECTORS)
            && matches!(self.current_token(), Token::BarBar)
        {
            expr = self.build_binary_expr(expr, |p| p.parse_bool_and_expr())?;
        }

        Ok(expr)
    }
    fn parse_bool_and_expr(&mut self) -> R<Box<Expression>> {
        // a && b
        let mut expr = self.parse_comparison_expr()?;

        while !self
            .restrictions
            .contains(Restrictions::STOP_CONDITION_CONNECTORS)
            && matches!(self.current_token(), Token::AmpAmp)
        {
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
                | Token::IdentityEql
                | Token::IdentityNeq
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
        let span = lhs.span.clone().to(rhs.span);
        let kind = ExpressionKind::Binary(op, lhs, rhs);
        let expr = self.build_expr(kind, span);

        Ok(expr)
    }
}

impl Parser {
    fn parse_cast_expr(&mut self) -> R<Box<Expression>> {
        let mut expr = self.parse_kw_prefix_expr()?;

        loop {
            if self.eat(Token::As) {
                let is_try_cast = self.eat_question();
                let ty = self.parse_type()?;

                let span = expr.span.clone().to(ty.span);
                let kind = if is_try_cast {
                    ExpressionKind::CastAsTry(expr, ty)
                } else {
                    ExpressionKind::CastAs(expr, ty)
                };
                expr = self.build_expr(kind, span);
                continue;
            }

            if self.eat(Token::Is) {
                let ty = self.parse_type()?;
                let span = expr.span.clone().to(ty.span);
                expr = self.build_expr(ExpressionKind::TypeIs(expr, ty), span);
                continue;
            }

            break;
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
                self.parse_reference_modifier();
                let expr = self.parse_prefix_expr()?;
                return Ok(self.build_expr(ExpressionKind::Reference(expr), lo.to(self.hi_span())));
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
        loop {
            let mut lo = self.lo_span();

            if pre_consumed_dot {
                lo = self.previous().unwrap().span;
            }

            let qualified = self.eat(Token::ColonColon);
            // `.` selects an instance member; `::` selects a namespace/type member.
            if qualified || self.eat(Token::Dot) || pre_consumed_dot {
                pre_consumed_dot = false; // reset for next iter
                // parsing tuple index: `foo.<integer>`
                if !qualified
                    && matches!(
                        self.current_token(),
                        Token::Integer {
                            base: Base::Decimal,
                            ..
                        }
                    )
                {
                    let c = self.parse_literal()?;
                    let k = ExpressionKind::TupleAccess(expr, AnonConst { value: c });
                    let span = lo.to(self.hi_span());
                    expr = self.build_expr(k, span);
                    continue;
                }

                // field access: `foo.<ident>`
                let lo = expr.span;
                let kind = ExpressionKind::Member {
                    target: expr,
                    name: self.parse_member_identifier()?,
                    qualified,
                };
                let span = lo.to(self.hi_span());
                expr = self.build_expr(kind, span);
                continue;
            }

            // Both generic arguments and value subscripts use brackets. Keep
            // both syntactic interpretations until the receiver is resolved.
            if self.matches(Token::LBracket) {
                let lo = expr.span;
                let (type_arguments, index) = self.parse_bracket_suffix()?;
                let kind = match type_arguments {
                    Some(type_arguments) => ExpressionKind::Specialize {
                        target: expr,
                        type_arguments,
                        index,
                    },
                    None => ExpressionKind::Index {
                        target: expr,
                        index: index.expect("expression-only bracket suffix"),
                    },
                };
                expr = self.build_expr(kind, lo.to(self.hi_span()));
                continue;
            }

            // parsing call expr: `foo(<expr_arguments>)`
            if self.matches(Token::LParen) {
                expr = self.parse_call_expr(expr)?;
                continue;
            }

            // parsing optional chaining: `foo?.member`
            // The `?.` wraps the expression BEFORE it (like Swift)
            // So `a?.b` becomes Member(OptionalUnwrap(a), b)
            if self.eat(Token::QuestionDot) {
                *is_optional_chain = true;

                // Wrap the current expression in OptionalUnwrap
                let span = expr.span.to(self.hi_span());
                let kind = ExpressionKind::OptionalUnwrap(expr);
                expr = self.build_expr(kind, span);

                // The dot is part of the `?.` token, so continue parsing the member/tuple access
                pre_consumed_dot = true;
                continue;
            }

            if self.eat(Token::Bang) {
                let span = expr.span.to(self.hi_span());
                let kind = ExpressionKind::Propagate(expr);
                expr = self.build_expr(kind, span);
                continue;
            }

            let before = self.cursor;
            expr = self.try_parse_struct_literal(expr)?;
            if self.cursor == before {
                break;
            }
        }

        Ok(expr)
    }

    fn parse_postfix_expr(&mut self) -> R<Box<Expression>> {
        let mut expr = self.parse_primary_expr()?;

        let mut has_optional_chain = false;

        expr = self.parse_postfix_expr_suffix(expr, &mut has_optional_chain)?;

        if has_optional_chain {
            let span = expr.span;
            let node = ExpressionKind::OptionalEvaluation(expr);
            expr = self.build_expr(node, span);
        }

        Ok(expr)
    }
}

impl Parser {
    fn parse_binding_initializer(&mut self) -> R<Box<Expression>> {
        self.with_restrictions(
            self.restrictions | Restrictions::STOP_CONDITION_CONNECTORS,
            Self::parse_assignment_expr,
        )
    }

    fn parse_condition(&mut self) -> R<Box<Expression>> {
        use ast::AstVisitor;
        struct Validate {
            permitted: bool,
            invalid: Option<Span>,
        }
        impl AstVisitor for Validate {
            type Result = ();
            fn visit_expression(&mut self, expression: &Expression) {
                if self.invalid.is_some() {
                    return;
                }
                let permitted = self.permitted;
                match &expression.kind {
                    // These expressions establish their own condition/binding
                    // scopes, validated when their syntax is parsed.
                    ExpressionKind::Closure(_)
                    | ExpressionKind::If(_)
                    | ExpressionKind::Block(_)
                    | ExpressionKind::UnsafeBlock(_)
                    | ExpressionKind::Match(_) => {}
                    ExpressionKind::PatternBinding(binding)
                    | ExpressionKind::OptionalPatternBinding(binding) => {
                        if !permitted {
                            self.invalid = Some(expression.span);
                            return;
                        }
                        self.permitted = false;
                        self.visit_expression(&binding.expression);
                    }
                    ExpressionKind::Binary(BinaryOperator::BoolAnd, _, _) if permitted => {
                        ast::walk_expression(self, expression);
                    }
                    _ => {
                        self.permitted = false;
                        ast::walk_expression(self, expression);
                    }
                }
                self.permitted = permitted;
            }
        }
        let condition = self.with_restrictions(
            Restrictions::ALLOW_BINDING_CONDITION | Restrictions::NO_STRUCT_LITERALS,
            Self::parse_expression,
        )?;
        let mut validator = Validate {
            permitted: true,
            invalid: None,
        };
        validator.visit_expression(&condition);
        if let Some(span) = validator.invalid {
            return Err(Spanned::new(
                ParserError::InvalidBindingConditionPosition,
                span,
            ));
        }
        Ok(condition)
    }

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
        self.eat(Token::Var);
        let pattern = self.parse_pattern()?;
        if self.matches(Token::ColonEq) {
            return Err(self.err_at_current(ParserError::ConditionalShorthandBinding));
        }
        self.expect(Token::Assign)?;
        let expression = self.parse_binding_initializer()?;

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
        // var <ident> = <expr>, or shorthand optional unwrapping.
        if self.matches(Token::Let) {
            self.emit_error(ParserError::LetRemoved(None), self.lo_span());
            self.bump();
        } else {
            self.expect(Token::Var)?;
        }
        let identifier = self.parse_identifier()?;
        let pattern = Pattern {
            id: self.next_id(),
            span: identifier.span,
            kind: PatternKind::Identifier(identifier),
        };

        if self.matches(Token::ColonEq) {
            return Err(self.err_at_current(ParserError::ConditionalShorthandBinding));
        }
        let expression = if self.eat(Token::Assign) {
            self.parse_binding_initializer()?
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
        let s = expr.span;
        let k = ExpressionKind::Call(expr, args);
        return Ok(self.build_expr(k, s.to(self.hi_span())));
    }
}

impl Parser {
    /// Try only the header speculatively. Once `=>` is consumed, body errors
    /// belong to the closure rather than triggering tuple-expression fallback.
    fn try_parse_arrow_closure(&mut self, lo: Span) -> R<Option<Box<Expression>>> {
        let checkpoint = self.checkpoint();
        let header: R<(FunctionSignature, bool)> = (|| {
            let mut prototype = self.parse_closure_prototype()?;
            let is_async = self.eat(Token::Async);
            if is_async && prototype.output.is_none() && self.eat(Token::RArrow) {
                prototype.output = Some(self.parse_type()?);
            }
            let signature = FunctionSignature {
                prototype,
                span: lo.to(self.hi_span()),
            };
            self.expect(Token::EqArrow)?;
            Ok((signature, is_async))
        })();
        let (signature, is_async) = match header {
            Ok(header) => header,
            Err(_) => {
                self.restore(checkpoint);
                return Ok(None);
            }
        };

        // A closure establishes its own condition and struct-literal context.
        let body = self.with_restrictions(
            self.restrictions
                - (Restrictions::ALLOW_BINDING_CONDITION
                    | Restrictions::STOP_CONDITION_CONNECTORS
                    | Restrictions::NO_STRUCT_LITERALS),
            |parser| {
                if is_async {
                    parser.parse_block_expression()
                } else {
                    parser.parse_expression()
                }
            },
        )?;
        let span = lo.to(self.hi_span());
        let closure = ClosureExpression {
            signature,
            is_async,
            body,
            span,
        };
        Ok(Some(
            self.build_expr(ExpressionKind::Closure(closure), span),
        ))
    }

    fn try_parse_move_closure_expression(&mut self) -> R<Option<Box<Expression>>> {
        if !self.matches_contextual_identifier("move") {
            return Ok(None);
        }
        let checkpoint = self.checkpoint();
        let lo = self.lo_span();
        self.bump();
        if !self.matches(Token::LParen) {
            self.restore(checkpoint);
            return Ok(None);
        }
        let closure = self.try_parse_arrow_closure(lo)?;
        if closure.is_none() {
            self.restore(checkpoint);
        } else {
            self.emit_error(ParserError::MoveClosureRemoved, lo);
        }
        Ok(closure)
    }

    fn parse_closure_prototype(&mut self) -> R<FunctionPrototype> {
        let inputs = self.parse_delimiter_sequence(Delimiter::Parenthesis, Token::Comma, |p| {
            p.parse_closure_parameter()
        })?;
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
                span: ident.span,
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

        let (items, trailing) =
            self.with_restrictions(self.restrictions - Restrictions::NO_STRUCT_LITERALS, |p| {
                p.parse_delimiter_sequence_trailing(Delimiter::Parenthesis, Token::Comma, |p| {
                    p.parse_expression()
                })
            })?;

        let span = lo.to(self.hi_span());

        let kind = if items.len() == 1 && !trailing {
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
            Token::FStringStart => self.parse_fstring_expression(),
            Token::Identifier { .. } if self.matches_contextual_identifier("move") => {
                if let Some(expr) = self.try_parse_move_closure_expression()? {
                    Ok(expr)
                } else {
                    self.parse_identifier_expression()
                }
            }
            Token::Identifier { .. } => self.parse_identifier_expression(),
            Token::Dot => self.parse_inferred_member_expression(),
            Token::LParen => {
                if let Some(closure) = self.try_parse_arrow_closure(self.lo_span())? {
                    Ok(closure)
                } else {
                    self.parse_tuple_expr()
                }
            }
            Token::LBracket => self.with_restrictions(
                self.restrictions - Restrictions::NO_STRUCT_LITERALS,
                Self::parse_collection_expr,
            ),
            Token::Case => self.parse_pattern_binding_condition(),
            Token::Let | Token::Var => self.parse_optional_binding_condition(),
            Token::Return => self.parse_return_expression(),
            Token::Break => self.parse_break_expression(),
            Token::Continue => self.parse_continue_expression(),
            Token::Unsafe => self.parse_unsafe_block_expression(),
            Token::Await => self.parse_await_expression(),
            Token::LBrace => self.parse_block_expression(),
            Token::Bar | Token::BarBar => Err(self.err_at_current(ParserError::LegacyPipeClosure)),
            Token::Underscore => {
                if !self.restrictions.contains(Restrictions::ALLOW_WILDCARD) {
                    self.emit_error(ParserError::DisallowedWildcardExpression, self.lo_span());
                }

                let lo = self.lo_span();
                let kind = ExpressionKind::Wildcard;
                self.bump();
                Ok(self.build_expr(kind, lo.to(self.hi_span())))
            }
            Token::Hash => self.parse_cfg_check_expression(),
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
        self.with_restrictions(
            self.restrictions
                - (Restrictions::NO_STRUCT_LITERALS | Restrictions::STOP_CONDITION_CONNECTORS),
            |p| p.parse_delimiter_sequence(delim, Token::Comma, |p| p.parse_expression_argument()),
        )
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

    fn parse_unsafe_block_expression(&mut self) -> R<Box<Expression>> {
        let lo = self.lo_span();
        self.expect(Token::Unsafe)?;
        let block = self.parse_block()?;
        let kind = ExpressionKind::UnsafeBlock(block);
        let span = lo.to(self.hi_span());
        Ok(self.build_expr(kind, span))
    }

    /// `await expr`
    fn parse_await_expression(&mut self) -> R<Box<Expression>> {
        let lo = self.lo_span();
        self.expect(Token::Await)?;
        let value = self.parse_expression()?;
        let kind = ExpressionKind::Await(value);
        Ok(self.build_expr(kind, lo.to(self.hi_span())))
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
        let condition = self.parse_condition()?;

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
            match self.parse_match_arm() {
                Ok(item) => {
                    arms.push(item);
                    if let Err(e) = self.expect_semi() {
                        self.emit_error(e.value, e.span);
                        self.synchronize_match_arm();
                    }
                }
                Err(e) => {
                    self.emit_error(e.value, e.span);
                    self.synchronize_match_arm();
                }
            }
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
        let has_case_keyword = self.eat(Token::Case);
        if !has_case_keyword && !is_wildcard_shorthand {
            if let Some(arm) = self.try_parse_match_arm_without_case(lo)? {
                return Ok(arm);
            }

            self.expect(Token::Case)?;
        }
        self.parse_match_arm_body(lo)
    }

    fn parse_match_arm_body(&mut self, lo: Span) -> R<MatchArm> {
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

    fn try_parse_match_arm_without_case(&mut self, lo: Span) -> R<Option<MatchArm>> {
        let checkpoint = self.checkpoint();
        match self.parse_match_arm_body(lo) {
            Ok(arm) => {
                self.emit_error(ParserError::ExpectedMatchArmCaseKeyword, lo);
                Ok(Some(arm))
            }
            Err(_) => {
                self.restore(checkpoint);
                Ok(None)
            }
        }
    }

    fn synchronize_match_arm(&mut self) {
        while !self.is_at_end() {
            if self.eat(Token::Semicolon) {
                return;
            }

            if self.matches(Token::Case)
                || self.matches(Token::RBrace)
                || (self.matches(Token::Underscore) && self.next_matches(1, Token::EqArrow))
            {
                return;
            }

            self.bump();
        }
    }
}
impl Parser {
    fn escape_percent_for_sprintf(segment: &str) -> String {
        if !segment.contains('%') {
            return segment.to_string();
        }
        segment.replace('%', "%%")
    }

    fn parse_fstring_expression(&mut self) -> R<Box<Expression>> {
        let lo = self.lo_span();
        self.expect(Token::FStringStart)?;

        let mut text = String::new();
        let mut arguments: Vec<ExpressionArgument> = vec![];

        while !self.matches(Token::FStringEnd) && !self.is_at_end() {
            match self.current_token() {
                Token::FStringText { value } => {
                    if arguments.is_empty() {
                        text.push_str(value);
                    } else {
                        text.push_str(&Self::escape_percent_for_sprintf(value));
                    }
                    self.bump();
                }
                Token::FStringExprStart => {
                    if arguments.is_empty() {
                        text = Self::escape_percent_for_sprintf(&text);
                    }
                    self.bump(); // consume FStringExprStart

                    text.push_str("%v");
                    let expression = self.with_restrictions(
                        self.restrictions - Restrictions::NO_STRUCT_LITERALS,
                        Self::parse_expression,
                    )?;
                    let span = expression.span;
                    arguments.push(ExpressionArgument {
                        label: None,
                        expression,
                        span,
                    });

                    self.expect(Token::FStringExprEnd)?;
                }
                _ => return Err(self.err_at_current(ParserError::ExpectedExpression)),
            }
        }

        self.expect(Token::FStringEnd)?;
        let span = lo.to(self.hi_span());

        if arguments.is_empty() {
            return Ok(self.build_expr(
                ExpressionKind::Literal(Literal::String { value: text }),
                span,
            ));
        }

        let format_expr = self.build_expr(
            ExpressionKind::Literal(Literal::String { value: text }),
            span,
        );
        let format_span = format_expr.span;
        arguments.insert(
            0,
            ExpressionArgument {
                label: None,
                expression: format_expr,
                span: format_span,
            },
        );

        let std_identifier = Identifier {
            symbol: self.intern_symbol("std"),
            span,
        };
        let sprintf_identifier = Identifier {
            symbol: self.intern_symbol("sprintf"),
            span,
        };
        let std_expr = self.build_expr(ExpressionKind::Identifier(std_identifier), span);
        let callee = self.build_expr(
            ExpressionKind::Member {
                target: std_expr,
                name: sprintf_identifier,
                qualified: true,
            },
            span,
        );

        Ok(self.build_expr(ExpressionKind::Call(callee, arguments), span))
    }

    fn parse_literal(&mut self) -> R<Box<Expression>> {
        let literal = match self.current_token() {
            Token::Integer {
                value,
                base,
                suffix,
            } => Literal::Integer {
                value: value.clone(),
                base: *base,
                suffix: *suffix,
            },
            Token::Float { value, .. } => Literal::Float {
                value: value.clone(),
            },
            Token::String { value } => Literal::String {
                value: value.clone(),
            },
            Token::Rune { value } => Literal::Rune {
                value: value.clone(),
            },
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
    fn parse_function(
        &mut self,
        mode: FnParseMode,
        is_unsafe: bool,
    ) -> R<(Identifier, DeclarationKind)> {
        // func <name> <type_parameters>? (<parameter list>) <async?> -> <return_type>? <where_clause>?
        self.expect(Token::Function)?;
        let identifier = self.parse_identifier()?;
        let func = self.parse_fn(mode, is_unsafe)?;
        Ok((identifier, DeclarationKind::Function(func)))
    }

    fn parse_fn(&mut self, mode: FnParseMode, is_unsafe: bool) -> R<Function> {
        let lo = self.lo_span();
        let type_parameters = self.parse_type_parameters()?;
        let parameters = self.parse_function_parameters()?;

        // `func foo() async -> T`
        let is_async = self.eat(Token::Async);

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
            is_unsafe,
            is_async,
            is_final: false,
            is_override: false,
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
        let lo = self.lo_span();
        let attributes = self.parse_attributes()?;
        if self.matches_contextual_identifier("self")
            || matches!(self.current_token(), Token::Amp | Token::AmpAmp)
        {
            return self.parse_self_parameter(lo, attributes);
        }

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
        } else if let Some(label) = label.as_ref() {
            *label
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

    fn parse_self_parameter(
        &mut self,
        lo: Span,
        attributes: AttributeList,
    ) -> R<FunctionParameter> {
        let referenced = self.eat_amp();
        if referenced {
            self.parse_reference_modifier();
        }
        let ident = self.parse_self()?;
        self.emit_error(ParserError::ExplicitReceiverRemoved, lo);
        let ty = Type {
            id: self.next_id(),
            span: ident.span,
            kind: TypeKind::ImplicitSelf,
        };

        Ok(FunctionParameter {
            id: self.next_id(),
            attributes,
            label: None,
            name: ident,
            annotated_type: Box::new(ty),
            default_value: None,
            is_variadic: false,
            span: lo.to(self.hi_span()),
        })
    }

    fn parse_self(&mut self) -> R<Identifier> {
        let ident = self.parse_identifier()?;

        if !self.symbol_eq(ident.symbol, "self") {
            return Err(self.err_at_current(ParserError::ExpectedSelf));
        }

        return Ok(ident);
    }
}

impl Parser {
    fn is_callable_shorthand_name(&self, symbol: Symbol) -> bool {
        // Removed categories retain only parsing recovery, so the declaration
        // diagnostic identifies the old name without unrelated arrow errors.
        matches!(
            symbol.as_str(),
            "Fn" | "AsyncFn" | "FnMut" | "FnOnce" | "AsyncFnMut" | "AsyncFnOnce"
        )
    }

    fn parse_callable_type_arguments(&mut self) -> R<TypeArguments> {
        let lo = self.lo_span();
        let inputs = self
            .parse_delimiter_sequence(Delimiter::Parenthesis, Token::Comma, |p| p.parse_type())?;
        let tuple_span = lo.to(self.hi_span());

        self.expect(Token::RArrow)?;
        let output = self.parse_type()?;

        let args = Box::new(Type {
            id: self.next_id(),
            span: tuple_span,
            kind: TypeKind::Tuple(inputs),
        });

        Ok(TypeArguments {
            span: lo.to(self.hi_span()),
            arguments: vec![TypeArgument::Type(args), TypeArgument::Type(output)],
        })
    }

    /// Recover a legacy separator only to produce a precise migration diagnostic.
    /// Recording the error still rejects the entire source file.
    fn eat_path_separator(&mut self) -> bool {
        if self.eat(Token::ColonColon) {
            true
        } else if self.eat(Token::Dot) {
            self.emit_error(
                ParserError::QualifiedPathSeparator,
                self.previous().unwrap().span,
            );
            true
        } else {
            false
        }
    }

    pub fn parse_path(&mut self) -> R<Path> {
        let start_span = self.lo_span();

        let mut segments = Vec::new();
        loop {
            let segment = self.parse_path_segment()?;
            segments.push(segment);
            if self.eat_path_separator() {
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
        let arguments =
            if self.is_callable_shorthand_name(identifier.symbol) && self.matches(Token::LParen) {
                Some(self.parse_callable_type_arguments()?)
            } else {
                self.parse_optional_type_arguments()?
            };

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
    fn expr_to_path(&mut self, expr: &Expression) -> Option<Path> {
        match &expr.kind {
            ExpressionKind::Identifier(identifier) => {
                let segment = PathSegment {
                    id: expr.id,
                    identifier: *identifier,
                    arguments: None,
                    span: expr.span,
                };
                Some(Path {
                    span: expr.span,
                    segments: vec![segment],
                })
            }
            ExpressionKind::Member {
                target,
                name,
                qualified,
            } => {
                if !qualified {
                    self.emit_error(
                        ParserError::QualifiedPathSeparator,
                        Span {
                            start: target.span.end,
                            end: name.span.start,
                            file: expr.span.file,
                        },
                    );
                }
                let mut path = self.expr_to_path(target)?;
                let segment = PathSegment {
                    id: self.next_index.borrow_mut().next(),
                    identifier: *name,
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
                ..
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
        let path = if let ExpressionKind::InferredMember { name } = &expr.kind {
            ConstructorPath::Inferred {
                name: *name,
                span: expr.span,
            }
        } else {
            let Some(path) = self.expr_to_path(&expr) else {
                return Err(Spanned::new(ParserError::ExpectedPathExpression, expr.span));
            };
            ConstructorPath::Qualified { path }
        };

        // Parse the struct literal with the converted path
        let span = expr.span;
        self.parse_struct_literal(path, span)
    }

    fn looks_like_struct_literal(&self) -> bool {
        if self.next_matches(1, Token::DotDot) {
            return true;
        }
        if !matches!(self.next(1), Some(Token::Identifier { .. })) {
            return false;
        }
        self.next_matches(2, Token::Comma)
            || (self.next_matches(2, Token::Colon)
                && (self.next_matches(4, Token::Comma)
                    || matches!(
                        self.next(3),
                        Some(
                            Token::String { .. }
                                | Token::FStringStart
                                | Token::Integer { .. }
                                | Token::Float { .. }
                                | Token::True
                                | Token::False
                                | Token::Nil
                        )
                    )))
    }

    fn parse_struct_literal(&mut self, path: ConstructorPath, span: Span) -> R<Box<Expression>> {
        let (fields, base) = self.parse_expression_field_list()?;
        let literal = StructLiteral { path, fields, base };
        let kind = ExpressionKind::StructLiteral(literal);
        let span = span.to(self.hi_span());
        Ok(self.build_expr(kind, span))
    }

    fn parse_expression_field_list(
        &mut self,
    ) -> R<(Vec<ExpressionField>, Option<Box<Expression>>)> {
        let mut base = None;
        let entries = self.parse_delimiter_sequence(Delimiter::Brace, Token::Comma, |p| {
            if base.is_some() {
                p.emit_error(ParserError::StructUpdateBaseMustBeLast, p.lo_span());
            }
            if p.eat(Token::DotDot) {
                base = Some(p.parse_expression()?);
                Ok(None)
            } else {
                p.parse_expression_field().map(Some)
            }
        })?;
        let fields: Vec<_> = entries.into_iter().flatten().collect();
        let mut names = std::collections::HashSet::new();
        for field in &fields {
            let name = match (&field.label, &field.expression.kind) {
                (Some(label), _) => label.identifier,
                (None, ExpressionKind::Identifier(name)) => *name,
                _ => {
                    self.emit_error(ParserError::InvalidFieldShorthand, field.span);
                    continue;
                }
            };
            if !names.insert(name.symbol) {
                self.emit_error(ParserError::DuplicateNamedField(name.symbol), name.span);
            }
        }
        Ok((fields, base))
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
    fn bin_op_non_assign(k: &Token) -> Option<BinaryOperator> {
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

            Token::IdentityEql => Some(BinaryOperator::IdentityEql),
            Token::IdentityNeq => Some(BinaryOperator::IdentityNeq),
            Token::Eql => Some(BinaryOperator::Eql),
            Token::Neq => Some(BinaryOperator::Neq),
            Token::Geq => Some(BinaryOperator::Geq),
            Token::Leq => Some(BinaryOperator::Leq),

            Token::RChevron => Some(BinaryOperator::Gt),
            Token::LChevron => Some(BinaryOperator::Lt),
            _ => None,
        }
    }

    fn bin_op_assign(k: &Token) -> Option<BinaryOperator> {
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
pub(crate) enum ParserError {
    Expected(Token, Token),
    ExpectedIdentifier,
    ExpectedCfgIdentifier,
    ExpectedSemiColon,
    QualifiedPathSeparator,
    LegacyImplDeclaration,
    ExpectedConformanceTo,
    StaticFunctionHasReceiver,
    DuplicateMethodModifier,
    InvalidMethodModifier,
    LifecycleRequiresExtension,
    InvalidLifecycleModifier,
    InvalidInitializerSignature,
    InitializerReceiver,
    WeakStorageRemoved,
    ConditionalShorthandBinding,
    TypedShorthandDeclaration,
    ReferenceConstModifier,
    MutableReferenceRemoved,
    ExplicitReceiverRemoved,
    ReferencePatternRemoved,
    MoveClosureRemoved,
    RemovedCallableKind(Symbol),
    LegacyPipeClosure,
    EnumPayloadVisibility,
    DuplicateEnumPayloadField(Symbol),
    DuplicateNamedField(Symbol),
    StructUpdateBaseMustBeLast,
    InvalidNamedPatternRest,
    InvalidFieldShorthand,
    ExpectedEnumPayloadSeparator,
    InvalidBindingConditionPosition,
    ExpectedDeclaration,
    ExpectedTopLevelDeclaration,
    TopLevelVariableMustBeStatic,
    ExpectedType,
    ExpectedInterfaceSetMember,
    ExpectedGenericRequirement,
    ExpectedMatchingPattern,
    ExpectedMatchArmCaseKeyword,
    ExpectedElseBlock,
    ExpectedExpression,
    InvalidCollectionType,
    ExpectedStaticVar,
    LetRemoved(Option<Symbol>),
    RelaxedBoundRemoved,
    MissingStaticTypeAnnotation,
    MissingStaticInitializer,
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
    ExpectedParameterNameOrLabel,
    ExpectedParameterName,
    ExpectedSelf,
    ExpectedExternAbiString,
    ExpectedExternDeclaration,
    DissallowedExternDeclaration,
    ExternFunctionBodyNotAllowed,
    DisallowedStructLiteral,
    ExpectedPathExpression,
    ExpectedComputedPropertyAccessor,
    ComputedPropertyAccessorSignatureRemoved,
    InvalidSubscriptSignature,
    InvalidSubscriptAccessor,
    DuplicateSubscriptAccessor,
    MissingSubscriptRead,
    MissingComputedPropertyGetter,
    DuplicateComputedPropertyAccessor,
    UnsafeModifierRequiresFunction,
    UnsafeAttributeRemoved,
    DeinitRemoved,
    UnexpectedSemicolonInList { context: &'static str },
    DuplicateModuleDecl,
    ModuleDeclNameMismatch { declared: String, expected: String },
    ModuleDeclInRoot,
}

impl Display for ParserError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use ParserError::*;
        match self {
            Expected(expected, found) => {
                write!(f, "expected `{expected}`, found `{found}`")
            }
            ExpectedIdentifier => f.write_str("expected identifier"),
            ExpectedCfgIdentifier => {
                f.write_str("expected 'cfg' following '#' in configuration expression")
            }
            ExpectedSemiColon => f.write_str("expected ';'"),
            QualifiedPathSeparator => f.write_str("qualified paths require `::` instead of `.`"),
            LegacyImplDeclaration => f.write_str(
                "implementation declarations use `extend Type` or `conform Type to Interface`",
            ),
            ExplicitReceiverRemoved => f.write_str("self is implicit; declare storage receivers with `extend &T` or `conform &T to I`"),
            ReferencePatternRemoved => f.write_str("reference patterns were removed; bind values in matches or dereference local initializers"),
            MoveClosureRemoved => f.write_str("`move` closures were removed; closures share captured variables"),
            RemovedCallableKind(name) => write!(f, "`{name}` was removed; use `{}`", if name.as_str().starts_with("Async") { "AsyncFn" } else { "Fn" }),
            MutableReferenceRemoved => f.write_str("safe references use `&`; `&mut` has been removed"),
            ReferenceConstModifier => f.write_str("`&const T` is removed; write `&T`"),
            EnumPayloadVisibility => f.write_str("enum payload fields inherit the variant’s visibility; remove the field visibility modifier"),
            DuplicateEnumPayloadField(name) => write!(f, "duplicate enum payload field `{name}`"),
            DuplicateNamedField(name) => write!(f, "duplicate named field `{name}`"),
            StructUpdateBaseMustBeLast => write!(f, "a struct update base must appear once and at the end"),
            InvalidNamedPatternRest => write!(f, "`..` must appear once, at the end of a named pattern"),
            InvalidFieldShorthand => write!(f, "field shorthand requires a single identifier"),
            ExpectedEnumPayloadSeparator => {
                f.write_str("expected a comma or newline between enum payload fields")
            }
            TypedShorthandDeclaration => f.write_str(
                "shorthand declarations do not take type annotations; use `var name: Type = value`",
            ),
            ConditionalShorthandBinding => {
                f.write_str("conditional bindings use `var` or `case` with `=`, not `:=`")
            }
            InvalidBindingConditionPosition => {
                f.write_str("binding conditions must be standalone or joined with `&&`")
            }
            StaticFunctionHasReceiver => {
                f.write_str("a static function cannot declare a self receiver")
            }
            ExpectedConformanceTo => f.write_str("expected `to` after the conformance target type"),
            ExpectedDeclaration => f.write_str("expected declaration"),
            ExpectedTopLevelDeclaration => f.write_str("expected top-level declaration"),
            TopLevelVariableMustBeStatic => f.write_str(
                "top-level and namespace variables must use `static var`",
            ),
            ExpectedType => f.write_str("expected type"),
            ExpectedInterfaceSetMember => {
                f.write_str("interface-set members must be interface paths")
            }
            ExpectedGenericRequirement => f.write_str("expected generic requirement"),
            ExpectedMatchingPattern => f.write_str("expected a matching pattern"),
            ExpectedMatchArmCaseKeyword => f.write_str("expected 'case' before match arm"),
            ExpectedElseBlock => f.write_str("expected 'else' block"),
            ExpectedExpression => f.write_str("expected expression"),
            InvalidCollectionType => f.write_str("invalid collection type"),
            ExpectedStaticVar => f.write_str("expected `var` after `static`"),
            LetRemoved(Some(name)) => {
                write!(f, "`let` was removed; declare this as `{name} := ...`")
            }
            LetRemoved(None) => f.write_str("`let` was removed; write `var` instead"),
            RelaxedBoundRemoved => f.write_str(
                "`!` bounds were removed; every type is escapable, so delete this bound",
            ),
            MissingStaticTypeAnnotation => {
                f.write_str("static declarations require an explicit type annotation")
            }
            MissingStaticInitializer => f.write_str("static declarations require an initializer"),
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
            ExpectedParameterNameOrLabel => f.write_str("expected parameter name or label"),
            ExpectedParameterName => f.write_str("expected parameter name"),
            ExpectedSelf => f.write_str("expected 'self'"),
            ExpectedExternAbiString => f.write_str("expected extern ABI string"),
            ExpectedExternDeclaration => f.write_str("expected extern declaration"),
            DissallowedExternDeclaration => f.write_str("disallowed extern declaration"),
            ExternFunctionBodyNotAllowed => f.write_str("extern functions cannot have a body"),
            DisallowedStructLiteral => {
                f.write_str("struct literals are not allowed in this context")
            }
            ExpectedPathExpression => f.write_str(
                "expected a path expression (identifier, member access, or type specialization)",
            ),
            ExpectedComputedPropertyAccessor => {
                f.write_str("computed properties are get-only; use `get { ... }` with implicit self")
            }
            InvalidSubscriptSignature => f.write_str("subscript requires one or more fixed index parameters, no defaults or variadics, and an element type"),
            InvalidSubscriptAccessor => f.write_str("expected `get`, `set(value)`, or `address` with implicit self and a synchronous body"),
            DuplicateSubscriptAccessor => f.write_str("duplicate subscript accessor"),
            MissingSubscriptRead => f.write_str("subscript must provide get or address; setter-only declarations are not supported"),
            MissingComputedPropertyGetter => f.write_str("computed property must declare a getter"),
            DuplicateComputedPropertyAccessor => {
                f.write_str("duplicate computed property accessor")
            }
            ComputedPropertyAccessorSignatureRemoved => f.write_str("computed getters use `get { ... }` with implicit self; receiver parameters, async and result annotations are not supported"),
            WeakStorageRemoved => f.write_str(
                "`weak` storage was removed; store a `std::weak::Weak[T]` and read it with `value()`",
            ),
            LifecycleRequiresExtension => f.write_str("init declarations belong in extend blocks"),
            InvalidLifecycleModifier => f.write_str("invalid init modifier combination"),
            DeinitRemoved => f.write_str(
                "`deinit` was removed; the garbage collector reclaims memory, so release resources with an explicit method such as `close()`",
            ),
            InvalidInitializerSignature => {
                f.write_str("init must be synchronous")
            }
            InitializerReceiver => f.write_str(
                "init has implicit initializing self; do not declare a receiver parameter",
            ),
            LegacyPipeClosure => f.write_str(
                "closures use `(parameters) => body`; pipe closures are no longer supported",
            ),
            DuplicateMethodModifier => f.write_str("duplicate class method modifier"),
            InvalidMethodModifier => {
                f.write_str("final/override require an instance function declaration")
            }
            UnsafeModifierRequiresFunction => {
                f.write_str("`unsafe` can only be applied to function declarations")
            }
            UnsafeAttributeRemoved => {
                f.write_str("`@unsafe` is no longer supported; use `unsafe func` instead")
            }
            UnexpectedSemicolonInList { context } => {
                write!(f, "unexpected semicolon in {}", context)
            }
            DuplicateModuleDecl => f.write_str("duplicate `mod` declaration in this module"),
            ModuleDeclNameMismatch { declared, expected } => write!(
                f,
                "`mod {}` does not match the enclosing module name `{}`",
                declared, expected
            ),
            ModuleDeclInRoot => {
                f.write_str("`mod` declarations are not allowed in the package root")
            }
        }
    }
}
struct FnParseMode {
    req_body: bool,
}

enum TopLevelItem {
    Decl(Declaration),
    Module(ModuleDecl),
}

enum Delimiter {
    /// `( ... )`
    Parenthesis,
    /// `{ ... }`
    Brace,
    /// `[ ... ]`
    Bracket,
}

impl Delimiter {
    fn open(&self) -> Token {
        match self {
            Delimiter::Parenthesis => Token::LParen,
            Delimiter::Brace => Token::LBrace,
            Delimiter::Bracket => Token::LBracket,
        }
    }

    fn close(&self) -> Token {
        match self {
            Delimiter::Parenthesis => Token::RParen,
            Delimiter::Brace => Token::RBrace,
            Delimiter::Bracket => Token::RBracket,
        }
    }
}

fn is_generic_type_disambiguating_token(token: &Token) -> bool {
    use Token::*;

    // `to` is contextual so ordinary parameter/local names can still use it.
    if matches!(token, Identifier { value } if value == "to") {
        return true;
    }
    if matches!(
        token,
        &RParen
            | &RBracket
            | &Bar
            | &EqArrow
            | &Async
            | &LBrace
            | &RBrace
            | &Dot
            | &ColonColon
            | &Comma
            | &Amp
            | &Semicolon
            | &EOF
            | &QuestionDot
            | &Bang
            | &Colon
            | &Question
            | &Assign
            | &As
            | &RChevron
            | &For // Recovery for a rejected legacy implementation header.
            | &Where // For `func foo() -> T[U] where ...` syntax
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
        const STOP_CONDITION_CONNECTORS = 1 << 4;
    }
}

impl Parser {
    fn with_restrictions<T>(&mut self, res: Restrictions, f: impl FnOnce(&mut Self) -> T) -> T {
        let old = self.restrictions;
        self.restrictions = res;
        let res = f(self);
        self.restrictions = old;
        res
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse::IntegerTypeSuffix;
    use crate::parse::lexer::Lexer;

    fn assert_nested_types_parse_once(open: &str, close: &str) {
        let depth = 10;
        let source = format!("{}int{}", open.repeat(depth), close.repeat(depth));
        let file = Lexer::new(&source, crate::span::FileID::new(0))
            .tokenize()
            .unwrap();
        let mut parser = Parser::new(file, NextNode::default());
        parser.parse_type().unwrap();
        let allocations = parser.next_index.borrow().allocations;
        assert!(
            allocations < 8 * (depth + 1),
            "nested type performed {allocations} node allocations"
        );
    }

    #[test]
    fn removed_mutable_references_report_one_deliberate_diagnostic() {
        for source in [
            "func edit(_ value: &mut int32) {}",
            "extend Counter { func edit(&mut self) {} }",
            "func main() { value := 1; alias := &mut value }",
        ] {
            let errors = parse_decls(source).unwrap_err();
            assert_eq!(
                errors
                    .iter()
                    .filter(|error| matches!(error.value, ParserError::MutableReferenceRemoved))
                    .count(),
                1,
                "{errors:?}"
            );
        }
    }

    #[test]
    fn nested_generic_types_parse_once() {
        assert_nested_types_parse_once("Box[", "]");
    }

    #[test]
    fn nested_parenthesized_types_parse_once() {
        assert_nested_types_parse_once("(", ")");
    }

    #[test]
    fn failed_type_lookahead_restores_compound_tokens() {
        let file = Lexer::new("[Box[T??], &&U + value]", crate::span::FileID::new(0))
            .tokenize()
            .unwrap();
        let original = format!("{:?}", file.tokens);
        let mut parser = Parser::new(file, NextNode::default());
        assert!(parser.parse_optional_type_arguments().unwrap().is_none());
        assert_eq!(parser.cursor, 0);
        assert_eq!(parser.next_index.borrow().next_index, 0);
        assert_eq!(format!("{:?}", parser.file.tokens), original);
    }

    #[test]
    fn preserves_ordinary_parameter_attributes() {
        let declaration = parse_one_decl("func f(@marker value: int) {}");
        let DeclarationKind::Function(function) = declaration.kind else {
            panic!("expected function");
        };
        let param = &function.signature.prototype.inputs[0];
        assert_eq!(param.attributes.len(), 1);
        assert_eq!(param.attributes[0].identifier.symbol.as_str(), "marker");
        assert_eq!(param.span.start.offset, 7);
    }

    #[test]
    fn qualified_and_instance_members_retain_distinct_syntax() {
        let expr = parse_expr_str("library\n::Counter[int]\n::new().value");
        let ExpressionKind::Member {
            target, qualified, ..
        } = &expr.kind
        else {
            panic!("expected instance field access");
        };
        assert!(!qualified);
        let ExpressionKind::Call(callee, _) = &target.kind else {
            panic!("expected constructor call");
        };
        assert!(matches!(
            callee.kind,
            ExpressionKind::Member {
                qualified: true,
                ..
            }
        ));
        let ty = parse_type_str("library::Container[library::Element]");
        let TypeKind::Nominal(path) = &ty.kind else {
            panic!("expected nominal type")
        };
        assert_eq!(path.segments.len(), 2);
    }

    #[test]
    fn qualified_import_forms_and_wildcard_asi() {
        let source =
            "import std::collections::{List, Dictionary as Map}\nexport std::task::*\nfunc f() {}";
        let decls = parse_decls(source).expect("qualified imports should parse");
        assert_eq!(decls.len(), 3);
        assert!(
            matches!(&decls[1].kind, DeclarationKind::Export(tree) if matches!(tree.kind, UseTreeKind::Glob))
        );
    }

    #[test]
    fn dotted_imports_and_type_paths_are_rejected() {
        for source in [
            "import std.collections.List",
            "type Item = library.Element",
            "func f() { value := library.Element {}; }",
        ] {
            let errors = parse_decls(source).expect_err("legacy qualified syntax must be rejected");
            assert!(
                errors
                    .iter()
                    .any(|error| matches!(error.value, ParserError::QualifiedPathSeparator))
            );
        }
    }

    fn parser(input: &str) -> Parser {
        let file = Lexer::new(input, crate::span::FileID::new(0))
            .tokenize()
            .expect("Lexing failed");
        Parser::new(file, NextNode::default())
    }

    fn parse_decls_and_module_decls(
        input: &str,
    ) -> Result<(Vec<Declaration>, Vec<ModuleDecl>), Vec<Spanned<ParserError>>> {
        parser(input)
            .parse()
            .map(|(decls, module_decls, _)| (decls, module_decls))
            .map_err(|(errors, _)| errors)
    }

    fn parse_decls(input: &str) -> Result<Vec<Declaration>, Vec<Spanned<ParserError>>> {
        parse_decls_and_module_decls(input).map(|(decls, _)| decls)
    }

    fn parse_one_decl(input: &str) -> Declaration {
        let decls = parse_decls(input).expect("Parse failed");
        assert_eq!(decls.len(), 1, "Expected exactly one declaration");
        decls.into_iter().next().unwrap()
    }

    fn parse_fragment<T>(input: &str, parse: impl FnOnce(&mut Parser) -> R<T>) -> T {
        let mut parser = parser(input);
        let result = parse(&mut parser).expect("Parse fragment failed");
        while parser.eat(Token::Semicolon) {}
        assert!(
            parser.is_at_end(),
            "unparsed tokens in {input:?}: {:?}",
            parser.current()
        );
        assert!(parser.errors.is_empty(), "{input}: {:?}", parser.errors);
        result
    }

    fn parse_expr_str(input: &str) -> Box<Expression> {
        parse_fragment(input, Parser::parse_expression)
    }

    fn parse_expr_err(input: &str) -> Vec<Spanned<ParserError>> {
        vec![
            parser(input)
                .parse_expression()
                .expect_err("expected parse failure"),
        ]
    }

    fn parse_type_str(input: &str) -> Box<Type> {
        parse_fragment(input, Parser::parse_type)
    }

    fn parse_pattern_str(input: &str) -> Pattern {
        parse_fragment(input, Parser::parse_pattern)
    }

    #[test]
    fn control_flow_allows_struct_literals_inside_delimiters() {
        for source in [
            "Flag { enabled: true }.enabled",
            "if (Flag { enabled: true }).enabled {}",
            "if accept(Flag { enabled: true }) {}",
            "if [Flag { enabled: true }].at(0).enabled {}",
            "if values.get(Key { index: 0 }) {}",
            "if { Flag { enabled: true }.enabled } {}",
            "if accept(() => { Flag { enabled: true } }) {}",
            "if f\"{Flag { enabled: true }.enabled}\" == \"true\" {}",
            "match (Flag { enabled: true }) { case value => {}; }",
        ] {
            parse_expr_str(source);
        }
        for source in [
            "func f() { while (Flag { enabled: true }).enabled { break } }",
            "func f() { for value in [Flag { enabled: true }] {} }",
            "func f() { guard (Flag { enabled: true }).enabled else { return } }",
        ] {
            parse_decls(source).expect(source);
        }
    }

    #[test]
    fn control_flow_still_rejects_bare_struct_literals() {
        for source in [
            "if Flag { enabled: true }.enabled {}",
            "if accept(true) && Flag { enabled: true }.enabled {}",
            "if (true) && Flag { enabled: true }.enabled {}",
            "match Flag { enabled: true } { case value => {} }",
        ] {
            let mut p = parser(source);
            let _ = p.parse_expression();
            assert!(
                p.errors
                    .iter()
                    .any(|e| matches!(e.value, ParserError::DisallowedStructLiteral)),
                "{source}: {:?}",
                p.errors
            );
        }
        let errors = parse_decls("func f() { while Flag { enabled: true }.enabled {} }")
            .expect_err("bare while condition");
        assert!(
            errors
                .iter()
                .any(|e| matches!(e.value, ParserError::DisallowedStructLiteral))
        );
    }

    // ==================== DECLARATION TESTS ====================

    #[test]
    fn test_mod_declaration_bare() {
        let (decls, module_decls) =
            parse_decls_and_module_decls("mod unix;").expect("Parse failed");
        assert!(decls.is_empty(), "mod should not produce a Declaration");
        assert_eq!(module_decls.len(), 1);
        let m = &module_decls[0];
        assert_eq!(m.name.symbol.as_str(), "unix");
        assert_eq!(m.visibility.level, VisibilityLevel::Inherent);
        assert!(m.attributes.is_empty());
    }

    #[test]
    fn test_mod_declaration_public() {
        let (_, module_decls) =
            parse_decls_and_module_decls("public mod unix;").expect("Parse failed");
        assert_eq!(module_decls.len(), 1);
        assert_eq!(module_decls[0].visibility.level, VisibilityLevel::Public);
    }

    #[test]
    fn test_mod_declaration_with_cfg_attr() {
        let (_, module_decls) =
            parse_decls_and_module_decls("@cfg(family(\"unix\")) public mod unix;")
                .expect("Parse failed");
        assert_eq!(module_decls.len(), 1);
        assert_eq!(module_decls[0].attributes.len(), 1);
        assert_eq!(
            module_decls[0].attributes[0].identifier.symbol.as_str(),
            "cfg"
        );
    }

    #[test]
    fn test_mod_declaration_alongside_items() {
        let (decls, module_decls) =
            parse_decls_and_module_decls("mod posix;\nfunc foo() {}").expect("Parse failed");
        assert_eq!(module_decls.len(), 1);
        assert_eq!(decls.len(), 1);
        assert!(matches!(decls[0].kind, DeclarationKind::Function(_)));
    }

    #[test]
    fn test_struct_declaration() {
        let decl = parse_one_decl("struct Point { x: int32; y: int32; }");
        assert!(matches!(&decl.kind, DeclarationKind::Struct(s) if s.fields.len() == 2));
    }

    #[test]
    fn comma_separated_fields_do_not_break_following_declarations() {
        let declarations = parse_decls("struct Inner { value: int32 }\nstruct Outer { inner: Inner, tag: string, }\nfunc main() {}")
            .expect("comma-separated fields");
        assert_eq!(declarations.len(), 3);
    }

    #[test]
    fn test_struct_readonly_fields() {
        let decl = parse_one_decl("struct Config { readonly value: int32; }");
        match &decl.kind {
            DeclarationKind::Struct(s) => {
                assert!(matches!(s.fields[0].mutability, Mutability::Immutable))
            }
            _ => panic!("Expected struct"),
        }
    }

    #[test]
    fn test_enum_declaration() {
        let decl = parse_one_decl("enum Color { case red, green, blue; }");
        match &decl.kind {
            DeclarationKind::Enum(e) => assert_eq!(e.cases[0].variants.len(), 3),
            _ => panic!("Expected enum"),
        }
    }

    #[test]
    fn test_enum_tuple_variants() {
        let decl = parse_one_decl("enum Result[T, E] { case ok(T), err(E); }");
        match &decl.kind {
            DeclarationKind::Enum(e) => {
                assert!(
                    matches!(&e.cases[0].variants[0].kind, VariantKind::Tuple(f) if f.len() == 1)
                );
            }
            _ => panic!("Expected enum"),
        }
    }

    #[test]
    fn test_interface_declaration() {
        let decl = parse_one_decl("interface Drawable { func draw(); }");
        assert!(matches!(&decl.kind, DeclarationKind::Interface(i) if i.declarations.len() == 1));
    }

    #[test]
    fn test_interface_conformances() {
        let decl = parse_one_decl(
            "interface Comparable: Equatable { func compare( other: &Self) -> int32; }",
        );
        match &decl.kind {
            DeclarationKind::Interface(i) => assert!(i.conformances.is_some()),
            _ => panic!("Expected interface"),
        }
    }

    #[test]
    fn test_function_declaration() {
        let decl = parse_one_decl("func add(a: int32, b: int32) -> int32 { return a + b; }");
        match &decl.kind {
            DeclarationKind::Function(f) => {
                assert_eq!(f.signature.prototype.inputs.len(), 2);
                assert!(f.signature.prototype.output.is_some());
            }
            _ => panic!("Expected function"),
        }
    }

    #[test]
    fn test_namespace_declaration() {
        let decl = parse_one_decl("namespace Math { const PI: int32 = 3; }");
        assert!(matches!(&decl.kind, DeclarationKind::Namespace(ns) if ns.declarations.len() == 1));
    }

    #[test]
    fn test_extern_block() {
        let decl = parse_one_decl(r#"extern "C" { func printf(fmt: *const int8) -> int32; }"#);
        assert!(
            matches!(&decl.kind, DeclarationKind::ExternBlock(ext) if ext.declarations.len() == 1)
        );
    }

    #[test]
    fn test_import_declaration() {
        let decl = parse_one_decl("import std::io::*");
        assert!(matches!(&decl.kind, DeclarationKind::Import(_)));
    }

    #[test]
    fn test_import_nested() {
        let decl = parse_one_decl("import std::{io, fs, net}");
        match &decl.kind {
            DeclarationKind::Import(tree) => {
                assert!(
                    matches!(&tree.kind, UseTreeKind::Nested { nodes, .. } if nodes.len() == 3)
                );
            }
            _ => panic!("Expected import"),
        }
    }

    #[test]
    fn test_impl_declaration() {
        // Test inherent impl
        let decl = parse_one_decl("extend int32 { const VALUE: int32 = 0; }");
        assert!(
            matches!(&decl.kind, DeclarationKind::Impl(impl_block) if impl_block.declarations.len() == 1 && impl_block.interface.is_none())
        );

        // Test trait impl
        let decl =
            parse_one_decl("conform Point to Hashable { static func hash() -> int64 { 0 }; }");
        assert!(
            matches!(&decl.kind, DeclarationKind::Impl(impl_block) if impl_block.interface.is_some())
        );
    }

    #[test]
    fn conformance_target_precedes_interface_and_keeps_generic_arguments() {
        let declaration = parse_one_decl(
            "conform[T: Copy] Box[T] to Readable[T] where T: Clone { func read() {}; }",
        );
        let DeclarationKind::Impl(implementation) = declaration.kind else {
            panic!("expected implementation node");
        };
        let TypeKind::Nominal(target) = &implementation.target.kind else {
            panic!("expected nominal target");
        };
        let TypeKind::Nominal(interface) = &implementation.interface.as_ref().unwrap().kind else {
            panic!("expected nominal interface");
        };
        assert_eq!(target.segments[0].identifier.symbol.as_str(), "Box");
        assert_eq!(interface.segments[0].identifier.symbol.as_str(), "Readable");
        assert!(target.segments[0].arguments.is_some());
        assert!(implementation.generics.where_clause.is_some());
        let ty = parse_type_str("library::Wrapper[int32]::Item");
        assert!(matches!(ty.kind, TypeKind::Nominal(path) if path.segments[1].arguments.is_some()));
        parse_one_decl("func pass(_ to: int32) -> int32 { to }");
    }

    #[test]
    fn g29_implicit_receivers_use_the_declared_target() {
        for target in ["Counter", "&Counter"] {
            let declaration = parse_one_decl(&format!(
                "extend {target} {{ func read(_ scale: int32) -> int32 {{ self.value * scale }}; static func make() {{}}; }}"
            ));
            let DeclarationKind::Impl(implementation) = declaration.kind else {
                panic!("extension")
            };
            let AssociatedDeclarationKind::Function(method) = &implementation.declarations[0].kind
            else {
                panic!("method")
            };
            assert!(
                matches!(
                    method.signature.prototype.inputs[0].annotated_type.kind,
                    TypeKind::ImplicitSelf
                ),
                "{target}: receiver must be Self, not &Self"
            );
            assert_eq!(
                method.signature.prototype.inputs[1].name.symbol.as_str(),
                "scale"
            );
            let AssociatedDeclarationKind::Function(method) = &implementation.declarations[1].kind
            else {
                panic!("static method")
            };
            assert!(method.signature.prototype.inputs.is_empty());
        }
    }

    #[test]
    fn static_functions_reject_every_explicit_receiver_mode() {
        for receiver in ["self", "&self", "&self"] {
            let source = format!("extend Counter {{ static func bad({receiver}) {{}}; }}");
            let errors = parse_decls(&source).expect_err("static receivers must be rejected");
            assert!(
                errors
                    .iter()
                    .any(|e| matches!(e.value, ParserError::StaticFunctionHasReceiver))
            );
        }
        assert!(parse_decls("static func free() {}").is_err());
    }

    #[test]
    fn local_shorthand_normalizes_to_an_inferred_mutable_declaration() {
        let DeclarationKind::Function(function) =
            parse_one_decl("func f() { value\n:=\n1; value = 2; }").kind
        else {
            panic!("function")
        };
        let block = function.block.unwrap();
        let StatementKind::Variable(local) = &block.statements[0].kind else {
            panic!("local")
        };
        assert_eq!(local.mutability, Mutability::Mutable);
        assert!(local.is_shorthand);
        assert!(local.ty.is_none());
        assert!(local.initializer.is_some());
        assert!(matches!(local.pattern.kind, PatternKind::Identifier(_)));
        for source in [
            "value := 1",
            "func f() { value :=; }",
            "func f() { var value := 1; }",
            "func f() { value: int32 := 1; }",
        ] {
            assert!(parse_decls(source).is_err(), "{source}");
        }
    }

    #[test]
    fn conditional_bindings_accept_writable_value_patterns() {
        for source in [
            "if var value = optional {}",
            "if case var .some(value) = optional {}",
            "if case .some(value) = optional {}",
        ] {
            let expression = parse_expr_str(source);
            let ExpressionKind::If(condition) = &expression.kind else {
                panic!("if")
            };
            assert!(matches!(
                condition.condition.kind,
                ExpressionKind::OptionalPatternBinding(_) | ExpressionKind::PatternBinding(_)
            ));
        }
        parse_one_decl(
            "func f() { while var value = next() {}; guard var value = optional else { return; }; }",
        );
    }

    #[test]
    fn let_reports_removed_syntax_with_a_replacement() {
        let messages = |source: &str| -> Vec<String> {
            parse_decls(source)
                .expect_err("`let` is removed")
                .into_iter()
                .map(|error| error.value.to_string())
                .collect()
        };
        assert_eq!(
            messages("func f() { let total = 1 }"),
            ["`let` was removed; declare this as `total := ...`"]
        );
        for source in [
            "func f() { let total: int32 = 1 }",
            "func f() { let (a, b) = (1, 2) }",
            "func f() { let later: int32; later = 1 }",
            "func f(o: Optional[int32]) { if let v = o {} }",
            "static let LIMIT: int32 = 1",
        ] {
            assert_eq!(
                messages(source),
                ["`let` was removed; write `var` instead"],
                "{source}"
            );
        }
    }

    #[test]
    fn binding_initializers_stop_before_condition_connectors_but_not_nested_operators() {
        let expression = parse_expr_str("if var value = produce(true && false) && value > 0 {}");
        let ExpressionKind::If(condition) = &expression.kind else {
            panic!("if")
        };
        let ExpressionKind::Binary(BinaryOperator::BoolAnd, left, _) = &condition.condition.kind
        else {
            panic!("conjunction")
        };
        let ExpressionKind::OptionalPatternBinding(binding) = &left.kind else {
            panic!("binding")
        };
        assert!(matches!(
            binding.expression.kind,
            ExpressionKind::Call(_, _)
        ));
        parse_expr_str("if var first = a && var second = b && first == second {}");
        parse_expr_str("if predicate(() => { if var value = optional {}; true }) {}");
        parse_expr_str("if { if true {}; true } {}");
    }

    #[test]
    fn conditional_shorthand_and_non_conjunctive_binding_positions_are_rejected() {
        for source in [
            "if value := optional {}",
            "if var value := optional {}",
            "if case .some(value) := optional {}",
        ] {
            let errors = parse_expr_err(source);
            assert!(
                errors
                    .iter()
                    .any(|e| matches!(e.value, ParserError::ConditionalShorthandBinding)),
                "{source}: {errors:?}"
            );
        }
        for source in [
            "if var value = optional || true {}",
            "if !(var value = optional) {}",
            "if predicate(var value = optional) {}",
            "if (var value = optional) {}",
        ] {
            let errors = parse_expr_err(source);
            assert!(
                errors
                    .iter()
                    .any(|e| matches!(e.value, ParserError::InvalidBindingConditionPosition)),
                "{source}: {errors:?}"
            );
        }
    }

    #[test]
    fn rejected_condition_recovers_through_its_nested_body() {
        let errors = parse_decls("func main() { if value := 1 { return; } }")
            .expect_err("invalid condition");
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(matches!(
            errors[0].value,
            ParserError::ConditionalShorthandBinding
        ));
    }

    #[test]
    fn class_headers_are_distinct_from_inline_structs() {
        let declaration = parse_one_decl(
            "public final class Box[T]: Base, Printable where T: Copy { readonly value: T }",
        );
        assert_eq!(declaration.visibility.level, VisibilityLevel::Public);
        let DeclarationKind::Class(class) = declaration.kind else {
            panic!("expected class")
        };
        assert!(class.is_final);
        assert!(class.generics.type_parameters.is_some());
        assert!(class.generics.where_clause.is_some());
        assert_eq!(class.fields[0].mutability, Mutability::Immutable);
        let declaration = parse_one_decl("namespace Models { class Entry {}; }");
        let DeclarationKind::Namespace(namespace) = declaration.kind else {
            panic!("namespace")
        };
        assert!(matches!(
            namespace.declarations[0].kind,
            NamespaceDeclarationKind::Class(_)
        ));
        assert!(parse_decls("func f() { class Local {} }").is_err());
        assert!(parse_decls("final struct Value {}").is_err());
    }

    #[test]
    fn class_method_modifiers_preserve_the_implicit_receiver() {
        let declaration = parse_one_decl("extend Box { final override func reset() {}; }");
        let DeclarationKind::Impl(block) = declaration.kind else {
            panic!("extend")
        };
        let AssociatedDeclarationKind::Function(function) = &block.declarations[0].kind else {
            panic!("function")
        };
        assert!(function.is_final && function.is_override);
        assert!(matches!(
            function.signature.prototype.inputs[0].annotated_type.kind,
            TypeKind::ImplicitSelf
        ));
        assert!(parse_decls("extend Box { final final func f() {} }").is_err());
        assert!(parse_decls("extend Box { override static func f() {} }").is_err());
    }

    #[test]
    fn lifecycle_declarations_have_distinct_ast_nodes() {
        let declaration = parse_one_decl(
            "extend Doc { required override init(_ value: int32) { super.init(value) }
 convenience init() { self.init(0) } }",
        );
        let DeclarationKind::Impl(block) = declaration.kind else {
            panic!("extend")
        };
        let AssociatedDeclarationKind::Initializer(init) = &block.declarations[0].kind else {
            panic!("init")
        };
        assert!(init.is_required && init.function.is_override);
        assert!(!init.is_convenience);
        assert_eq!(init.function.signature.prototype.inputs.len(), 1);
        assert!(
            matches!(&block.declarations[1].kind, AssociatedDeclarationKind::Initializer(init) if init.is_convenience)
        );
        // Contextual modifiers remain ordinary identifiers outside declarations.
        parse_one_decl("func f(_ required: int32, _ convenience: int32) {}");
    }

    #[test]
    fn initializer_keeps_its_explicit_result_annotation() {
        let declaration = parse_one_decl(
            "extend Doc { required init[D](from decoder: D) -> Result[Self, D::Error] {} }",
        );
        let DeclarationKind::Impl(block) = declaration.kind else {
            panic!("extend")
        };
        let AssociatedDeclarationKind::Initializer(init) = &block.declarations[0].kind else {
            panic!("init")
        };
        assert!(init.is_required);
        assert!(!matches!(
            init.function
                .signature
                .prototype
                .output
                .as_ref()
                .unwrap()
                .kind,
            TypeKind::ImplicitSelf
        ));
    }

    #[test]
    fn lifecycle_signatures_reject_unapproved_forms() {
        for source in [
            "extend Doc { init() async {} }",
            "extend Doc { init(&self) {} }",
            "extend Doc { init?() {} }",
            "extend Doc { final init() {} }",
            "extend Doc { required func f() {} }",
            "interface P { init() }",
            "conform Doc to P { init() {}; }",
            "init() {}",
        ] {
            assert!(parse_decls(source).is_err(), "accepted {source}");
        }
    }

    #[test]
    fn weak_storage_reports_removed_syntax_and_keeps_weak_contextual() {
        let declaration = parse_one_decl(
            "class Node { parent: int32 = 0\n readonly id: int32 = 1\n weak: int32 }",
        );
        let DeclarationKind::Class(class) = declaration.kind else {
            panic!("class")
        };
        assert!(class.fields[0].default_value.is_some());
        assert_eq!(class.fields[1].mutability, Mutability::Immutable);
        assert_eq!(class.fields[2].identifier.symbol.as_str(), "weak");
        parse_one_decl("func f() { weak := 1 }");
        for source in [
            "class Node { weak parent: Node? = .none }",
            "func f() { weak var target: Node? = .none }",
            "func f() { weak var target: Node? = .none }",
        ] {
            let errors = parse_decls(source).expect_err("weak storage was removed");
            assert_eq!(errors.len(), 1, "{source}: {errors:?}");
            assert!(matches!(errors[0].value, ParserError::WeakStorageRemoved));
        }
    }

    #[test]
    fn relaxed_bounds_report_their_removal() {
        for source in [
            "func forward[T: !Escapable & Clone](_ value: T) -> T { value }",
            "func forward[T](_ value: T) -> T where T: !Escapable { value }",
            "interface View: !Escapable, Inspectable {}",
            "interface View { type Element: !Escapable; }",
        ] {
            let errors = parse_decls(source).expect_err("relaxed bounds were removed");
            assert_eq!(errors.len(), 1, "{source}: {errors:?}");
            assert!(matches!(errors[0].value, ParserError::RelaxedBoundRemoved));
        }
    }

    #[test]
    fn arrow_closures_parse_without_changing_parenthesized_expressions() {
        for source in [
            "() => 42",
            "(x) => x",
            "(x: int32,) -> int32 => x",
            "(x) -> std::result::Result[int32, string] => .ok(x)",
            "(x) async -> List[int32] => { x }",
            "(x) -> List[int32] async => { x }",
            "(x) => (y) => x + y",
            "() async -> int32 => { 42 }",
            "(x)\n => x",
        ] {
            assert!(
                matches!(parse_expr_str(source).kind, ExpressionKind::Closure(_)),
                "not a closure: {source}"
            );
        }
        for source in ["()", "(1, 2)", "(value)", "move(value)", "(left | right)"] {
            assert!(
                !matches!(parse_expr_str(source).kind, ExpressionKind::Closure(_)),
                "misparsed {source}"
            );
        }
    }

    #[test]
    fn legacy_pipe_closures_are_rejected_with_a_migration_diagnostic() {
        for source in ["|| 1", "|x| x"] {
            let errors = parse_expr_err(source);
            assert!(!errors.is_empty(), "accepted {source}");
            if !source.starts_with("move") {
                assert!(
                    errors
                        .iter()
                        .any(|e| matches!(e.value, ParserError::LegacyPipeClosure))
                );
            }
        }
        // Once the arrow commits the parse, missing bodies are closure errors.
        assert!(
            parse_expr_err("() =>")
                .iter()
                .any(|e| matches!(e.value, ParserError::ExpectedExpression))
        );
    }

    #[test]
    fn named_enum_payloads_preserve_names_labels_and_readonly() {
        let declaration = parse_one_decl(
            "enum Event[T] { case item { readonly fixed: T, editable: int32 }; case empty {}; }",
        );
        let DeclarationKind::Enum(event) = declaration.kind else {
            panic!("enum")
        };
        let VariantKind::Struct(fields) = &event.cases[0].variants[0].kind else {
            panic!("named payload")
        };
        assert_eq!(fields.len(), 2);
        assert_eq!(fields[0].identifier.symbol.as_str(), "fixed");
        assert_eq!(fields[0].label.unwrap().identifier, fields[0].identifier);
        assert_eq!(fields[0].mutability, Mutability::Immutable);
        assert_eq!(fields[1].mutability, Mutability::Mutable);
        assert!(
            matches!(&event.cases[1].variants[0].kind, VariantKind::Struct(fields) if fields.is_empty())
        );
        parse_one_decl("enum Event { case click { x: int32\n y: int32\n } }");
    }

    #[test]
    fn enum_payload_fields_reject_visibility_modifiers() {
        for visibility in ["public", "private", "internal"] {
            for payload in [
                format!("{{ {visibility} value: int32 }}"),
                format!("({visibility} int32)"),
            ] {
                let source = format!("enum Event {{ case item {payload} }}");
                let errors = parse_decls(&source).expect_err("payload visibility is inherited");
                assert_eq!(errors.len(), 1, "{source}: {errors:?}");
                assert!(matches!(
                    errors[0].value,
                    ParserError::EnumPayloadVisibility
                ));
            }
        }
        parse_one_decl("public enum Event { case item { value: int32 }; case tuple(int32) }");
        parse_one_decl("struct Value { private field: int32 }");
    }

    #[test]
    fn named_enum_payloads_require_separators_and_unique_names() {
        let errors = parse_decls("enum Event { case click { x: int32, x: int32 } }")
            .expect_err("duplicate field");
        assert!(
            errors
                .iter()
                .any(|e| matches!(e.value, ParserError::DuplicateEnumPayloadField(_)))
        );
        let errors = parse_decls("enum Event { case click { x: int32 y: int32 } }")
            .expect_err("missing separator");
        assert!(
            errors
                .iter()
                .any(|e| matches!(e.value, ParserError::ExpectedEnumPayloadSeparator))
        );
    }

    #[test]
    fn implementation_headers_reject_legacy_or_mixed_syntax() {
        for source in ["impl Counter {}", "impl Readable for Counter {}"] {
            let errors = parse_decls(source).expect_err("legacy implementation syntax is rejected");
            assert!(
                errors
                    .iter()
                    .any(|e| matches!(e.value, ParserError::LegacyImplDeclaration))
            );
        }
        let errors = parse_decls("conform Counter Readable {}").expect_err("missing to");
        assert!(
            errors
                .iter()
                .any(|e| matches!(e.value, ParserError::ExpectedConformanceTo))
        );
        assert!(parse_decls("extend Readable for Counter {}").is_err());
    }

    #[test]
    fn test_type_alias_declaration() {
        let decl = parse_one_decl("type StringMap[V] = Map[string, V]");
        match &decl.kind {
            DeclarationKind::TypeAlias(ta) => {
                assert!(ta.generics.type_parameters.is_some());
                assert!(ta.ty.is_some());
            }
            _ => panic!("Expected type alias"),
        }
    }

    #[test]
    fn test_interface_set_type_alias() {
        let decl = parse_one_decl("type Codable = Encodable & Decodable");
        match &decl.kind {
            DeclarationKind::TypeAlias(alias) => {
                assert!(alias.ty.is_none());
                assert_eq!(alias.interface_set.as_ref().map(Vec::len), Some(2));
            }
            _ => panic!("Expected type alias"),
        }
    }

    // ==================== TYPE TESTS ====================

    #[test]
    fn test_nominal_type() {
        let ty = parse_type_str("Foo");
        assert!(matches!(ty.kind, TypeKind::Nominal(_)));
    }

    #[test]
    fn test_nominal_type_qualified() {
        let ty = parse_type_str("std::io::File");
        assert!(matches!(&ty.kind, TypeKind::Nominal(p) if p.segments.len() == 3));
    }

    #[test]
    fn test_nominal_type_with_generics() {
        let ty = parse_type_str("Map[string, int32]");
        match &ty.kind {
            TypeKind::Nominal(p) => assert!(p.segments[0].arguments.is_some()),
            _ => panic!("Expected nominal type"),
        }
    }

    #[test]
    fn test_callable_shorthand_type_single_arg() {
        let ty = parse_type_str("Fn(int32) -> int32");
        let TypeKind::Nominal(path) = &ty.kind else {
            panic!("Expected nominal type");
        };
        let args = path.segments[0]
            .arguments
            .as_ref()
            .expect("callable shorthand lowers to type arguments");
        assert_eq!(args.arguments.len(), 2);
        assert!(
            matches!(&args.arguments[0], TypeArgument::Type(ty) if matches!(&ty.kind, TypeKind::Tuple(items) if items.len() == 1 && matches!(items[0].kind, TypeKind::Nominal(_))))
        );
        assert!(
            matches!(&args.arguments[1], TypeArgument::Type(ty) if matches!(ty.kind, TypeKind::Nominal(_)))
        );
    }

    #[test]
    fn test_callable_shorthand_preserves_tuple_argument() {
        let ty = parse_type_str("Fn((int32, int32)) -> int32");
        let TypeKind::Nominal(path) = &ty.kind else {
            panic!("Expected nominal type");
        };
        let args = path.segments[0].arguments.as_ref().unwrap();
        let TypeArgument::Type(args_ty) = &args.arguments[0] else {
            panic!("Expected argument tuple");
        };
        let TypeKind::Tuple(inputs) = &args_ty.kind else {
            panic!("Expected argument tuple");
        };
        assert_eq!(inputs.len(), 1);
        assert!(matches!(&inputs[0].kind, TypeKind::Tuple(items) if items.len() == 2));
    }

    #[test]
    fn test_callable_shorthand_type_multi_arg() {
        let ty = parse_type_str("AsyncFn(int32, string) -> bool");
        let TypeKind::Nominal(path) = &ty.kind else {
            panic!("Expected nominal type");
        };
        let args = path.segments[0]
            .arguments
            .as_ref()
            .expect("callable shorthand lowers to type arguments");
        assert_eq!(args.arguments.len(), 2);
        assert!(matches!(
            &args.arguments[0],
            TypeArgument::Type(ty) if matches!(&ty.kind, TypeKind::Tuple(items) if items.len() == 2)
        ));
    }

    #[test]
    fn test_callable_shorthand_type_zero_arg() {
        let ty = parse_type_str("AsyncFn() -> int32");
        let TypeKind::Nominal(path) = &ty.kind else {
            panic!("Expected nominal type");
        };
        let args = path.segments[0]
            .arguments
            .as_ref()
            .expect("callable shorthand lowers to type arguments");
        assert!(matches!(
            &args.arguments[0],
            TypeArgument::Type(ty) if matches!(&ty.kind, TypeKind::Tuple(items) if items.is_empty())
        ));
    }

    #[test]
    fn test_pointer_type() {
        let ty = parse_type_str("*int32");
        assert!(matches!(ty.kind, TypeKind::Pointer(_, _)));
    }

    #[test]
    fn test_pointer_const_type() {
        let ty = parse_type_str("*const int32");
        assert!(matches!(
            ty.kind,
            TypeKind::Pointer(_, Mutability::Immutable)
        ));
    }

    #[test]
    fn test_reference_type() {
        let ty = parse_type_str("&int32");
        assert!(matches!(ty.kind, TypeKind::Reference(_)));
    }

    #[test]
    fn test_tuple_type_empty() {
        let ty = parse_type_str("()");
        assert!(matches!(ty.kind, TypeKind::Tuple(_)));
    }

    #[test]
    fn test_tuple_type() {
        let ty = parse_type_str("(int32, string, bool)");
        assert!(matches!(&ty.kind, TypeKind::Tuple(types) if types.len() == 3));
    }

    #[test]
    fn test_single_element_tuple_type() {
        let ty = parse_type_str("(int32,)");
        assert!(matches!(&ty.kind, TypeKind::Tuple(types) if types.len() == 1));
    }

    #[test]
    fn test_parenthesized_type_not_tuple() {
        let ty = parse_type_str("(int32)");
        assert!(matches!(ty.kind, TypeKind::Parenthesis(_)));
    }

    #[test]
    fn test_function_type() {
        let ty = parse_type_str("(int32, int32) -> int32");
        assert!(matches!(ty.kind, TypeKind::Function { .. }));
    }

    #[test]
    fn test_function_type_single_arg_no_comma() {
        // `(T) -> U` remains a single-argument function type, not a tuple-return trick.
        let ty = parse_type_str("(int32) -> int32");
        assert!(matches!(
            &ty.kind,
            TypeKind::Function { inputs, .. } if inputs.len() == 1
        ));
    }

    #[test]
    fn test_collection_type_list() {
        let ty = parse_type_str("[int32]");
        assert!(matches!(ty.kind, TypeKind::List(_)));
    }

    #[test]
    fn test_collection_type_slice() {
        let ty = parse_type_str("[int32; ..]");
        assert!(matches!(ty.kind, TypeKind::Slice(_)));
        let ty = parse_type_str("[[int32; ..]; ..]?");
        let TypeKind::Optional(inner) = ty.kind else {
            panic!("expected optional slice")
        };
        let TypeKind::Slice(inner) = inner.kind else {
            panic!("expected slice")
        };
        assert!(matches!(inner.kind, TypeKind::Slice(_)));
    }

    #[test]
    fn test_collection_type_dict() {
        let ty = parse_type_str("[string:int32]");
        assert!(matches!(ty.kind, TypeKind::Dictionary { .. }));
    }

    #[test]
    fn test_collection_type_array() {
        let ty = parse_type_str("[int32;10]");
        assert!(matches!(ty.kind, TypeKind::Array { .. }));
    }

    #[test]
    fn test_optional_type() {
        let ty = parse_type_str("int32?");
        assert!(matches!(ty.kind, TypeKind::Optional(_)));
    }

    #[test]
    fn test_optional_type_nested() {
        let ty = parse_type_str("int32??");
        match &ty.kind {
            TypeKind::Optional(inner) => assert!(matches!(inner.kind, TypeKind::Optional(_))),
            _ => panic!("Expected optional"),
        }
    }

    #[test]
    fn test_existential_type() {
        let ty = parse_type_str("any Drawable");
        assert!(matches!(ty.kind, TypeKind::BoxedExistential { .. }));
    }

    #[test]
    fn test_callable_shorthand_existential_type() {
        let ty = parse_type_str("any Fn(int32) -> int32");
        assert!(
            matches!(&ty.kind, TypeKind::BoxedExistential { interfaces } if interfaces.len() == 1)
        );
    }

    #[test]
    fn test_never_type() {
        let ty = parse_type_str("!");
        assert!(matches!(ty.kind, TypeKind::Never));
    }

    // ==================== GENERICS TESTS ====================

    #[test]
    fn test_type_parameters() {
        let decl = parse_one_decl("struct Box[T] { value: T; }");
        match &decl.kind {
            DeclarationKind::Struct(s) => {
                assert_eq!(
                    s.generics
                        .type_parameters
                        .as_ref()
                        .unwrap()
                        .parameters
                        .len(),
                    1
                );
            }
            _ => panic!("Expected struct"),
        }
    }

    #[test]
    fn test_type_parameter_bounds() {
        let decl = parse_one_decl("func sort[T: Comparable](list: [T]) { }");
        match &decl.kind {
            DeclarationKind::Function(f) => {
                let p = &f.generics.type_parameters.as_ref().unwrap().parameters[0];
                assert!(p.bounds.is_some());
            }
            _ => panic!("Expected function"),
        }
    }

    #[test]
    fn test_const_type_parameter() {
        let decl = parse_one_decl("struct Array[T, const N: isize] { data: *T; }");
        match &decl.kind {
            DeclarationKind::Struct(s) => {
                let params = s.generics.type_parameters.as_ref().unwrap();
                assert!(matches!(
                    params.parameters[1].kind,
                    TypeParameterKind::Constant { .. }
                ));
            }
            _ => panic!("Expected struct"),
        }
    }

    #[test]
    fn test_where_clause() {
        let decl = parse_one_decl("func foo[T]() where T: Eq { }");
        match &decl.kind {
            DeclarationKind::Function(f) => assert!(f.generics.where_clause.is_some()),
            _ => panic!("Expected function"),
        }
    }

    #[test]
    fn test_callable_shorthand_type_parameter_bounds() {
        let decl = parse_one_decl("func map[F: Fn(int32) -> int32](_ f: F) { }");
        match &decl.kind {
            DeclarationKind::Function(f) => {
                let p = &f.generics.type_parameters.as_ref().unwrap().parameters[0];
                let bounds = p.bounds.as_ref().expect("callable shorthand bound");
                assert_eq!(bounds.len(), 1);
            }
            _ => panic!("Expected function"),
        }
    }

    #[test]
    fn test_callable_shorthand_where_clause() {
        let decl = parse_one_decl("func map[F](_ f: F) where F: Fn(int32) -> int32 { }");
        match &decl.kind {
            DeclarationKind::Function(f) => assert!(f.generics.where_clause.is_some()),
            _ => panic!("Expected function"),
        }
    }

    #[test]
    fn test_callable_shorthand_interface_superface() {
        let decl = parse_one_decl("interface CallableInt: Fn(int32) -> int32 { }");
        match &decl.kind {
            DeclarationKind::Interface(i) => {
                let bounds = i.conformances.as_ref().expect("superinterface bounds");
                assert_eq!(bounds.bounds.len(), 1);
            }
            _ => panic!("Expected interface"),
        }
    }

    #[test]
    fn test_callable_shorthand_impl_interface() {
        let decl = parse_one_decl(
            "conform Point to Fn(int32) -> int32 { func call( args: int32) -> int32 { args }; }",
        );
        assert!(matches!(
            &decl.kind,
            DeclarationKind::Impl(impl_block) if impl_block.interface.is_some()
        ));
    }

    #[test]
    fn test_callable_legacy_generic_syntax_still_parses() {
        let ty = parse_type_str("Fn[(int32, int32), int32]");
        assert!(matches!(ty.kind, TypeKind::Nominal(_)));
    }

    #[test]
    fn test_callable_shorthand_requires_arrow() {
        let err = parse_decls("func map[F: Fn(int32)](_ f: F) { }")
            .expect_err("missing arrow should fail");
        assert!(!err.is_empty(), "expected parse error");
        assert!(matches!(
            err[0].value,
            ParserError::Expected(Token::RArrow, _)
        ));
    }

    // ==================== PATTERN TESTS ====================

    #[test]
    fn test_wildcard_pattern() {
        let pattern = parse_pattern_str("_");
        assert!(matches!(pattern.kind, PatternKind::Wildcard));
    }

    #[test]
    fn test_identifier_pattern() {
        let pattern = parse_pattern_str("x");
        assert!(matches!(pattern.kind, PatternKind::Identifier(_)));
    }

    #[test]
    fn test_tuple_pattern() {
        let pattern = parse_pattern_str("(a, b, c)");
        assert!(matches!(&pattern.kind, PatternKind::Tuple(pats, _) if pats.len() == 3));
    }

    #[test]
    fn reference_patterns_are_removed_in_every_binding_position() {
        for source in [
            "func f() { match value { case &x => x; } }",
            "func f() { match value { case &&x => x; } }",
            "func f() { var &x = value; }",
            "func f() { var (&x,) = value; }",
            "func f() { if case &x = value {} }",
        ] {
            let errors = parse_decls(source).expect_err("removed reference pattern");
            assert!(
                errors
                    .iter()
                    .any(|error| matches!(error.value, ParserError::ReferencePatternRemoved)),
                "{source}"
            );
        }
    }

    #[test]
    fn test_nested_pattern() {
        let pattern = parse_pattern_str("(a, (b, c))");
        match &pattern.kind {
            PatternKind::Tuple(pats, _) => {
                assert!(matches!(pats[1].kind, PatternKind::Tuple(_, _)))
            }
            _ => panic!("Expected tuple"),
        }
    }

    // ==================== STATEMENT TESTS ====================

    #[test]
    fn test_loop_statement() {
        let decl = parse_one_decl("func foo() { loop { break; } }");
        assert!(matches!(decl.kind, DeclarationKind::Function(_)));
    }

    #[test]
    fn test_while_statement() {
        let decl = parse_one_decl("func foo() { while true { break; } }");
        assert!(matches!(decl.kind, DeclarationKind::Function(_)));
    }

    #[test]
    fn test_for_statement() {
        // Test for-in loop via full function parsing
        let decl = parse_one_decl("func foo(xs: [int32]) { for x in xs { break } }");
        assert!(matches!(decl.kind, DeclarationKind::Function(_)));
    }

    #[test]
    fn test_for_await_statement() {
        let decl = parse_one_decl("func foo(xs: [int32]) async { for await x in xs { break } }");
        assert!(matches!(decl.kind, DeclarationKind::Function(_)));
    }

    #[test]
    fn test_defer_statement() {
        let decl = parse_one_decl("func foo() { defer { cleanup(); } }");
        assert!(matches!(decl.kind, DeclarationKind::Function(_)));
    }

    #[test]
    fn g43_inline_defer_wraps_one_expression() {
        let decl = parse_one_decl("func foo() { defer cleanup(value); after() }");
        let DeclarationKind::Function(function) = decl.kind else {
            panic!("function");
        };
        let body = function.block.unwrap();
        assert_eq!(body.statements.len(), 2);
        let StatementKind::Defer(block) = &body.statements[0].kind else {
            panic!("defer");
        };
        assert!(!block.has_declarations);
        assert_eq!(block.statements.len(), 1);
        let StatementKind::Expression(expression) = &block.statements[0].kind else {
            panic!("expression");
        };
        assert!(matches!(expression.kind, ExpressionKind::Call(..)));
        assert_ne!(block.id, block.statements[0].id);
        assert_ne!(block.id, expression.id);
        assert!(matches!(
            body.statements[1].kind,
            StatementKind::Expression(_)
        ));
    }

    #[test]
    fn g43_inline_defer_uses_existing_block_mir() {
        let diagnostics = crate::test_support::analyze_script_mir_diagnostics(
            "func emit(_ value: int32) {}; func main() { var value: int32 = 1; defer emit(value); defer value += 1; defer if value > 0 { emit(value) }; value = 2 }",
        );
        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    }

    #[test]
    fn test_guard_statement() {
        let decl = parse_one_decl("func foo(x: int32?) { guard x else { return; } }");
        assert!(matches!(decl.kind, DeclarationKind::Function(_)));
    }

    // ==================== EXPRESSION TESTS ====================

    #[test]
    fn test_literal_integer() {
        let expr = parse_expr_str("123");
        assert!(matches!(
            expr.kind,
            ExpressionKind::Literal(Literal::Integer { .. })
        ));
    }

    #[test]
    fn test_literal_float() {
        let expr = parse_expr_str("3.14");
        assert!(matches!(
            expr.kind,
            ExpressionKind::Literal(Literal::Float { .. })
        ));
    }

    #[test]
    fn test_literal_string() {
        let expr = parse_expr_str("\"hello\"");
        assert!(matches!(
            expr.kind,
            ExpressionKind::Literal(Literal::String { .. })
        ));
    }

    #[test]
    fn test_fstring_no_interpolation_lowers_to_string_literal() {
        let expr = parse_expr_str(r#"f"hello {{world}}""#);
        match &expr.kind {
            ExpressionKind::Literal(Literal::String { value }) => {
                assert_eq!(value, "hello {world}");
            }
            _ => panic!("expected string literal"),
        }
    }

    #[test]
    fn test_fstring_interpolation_lowers_to_std_sprintf_call() {
        let expr = parse_expr_str(r#"f"hello {name}""#);
        let ExpressionKind::Call(callee, args) = &expr.kind else {
            panic!("expected call expression");
        };

        assert_eq!(args.len(), 2);
        match &args[0].expression.kind {
            ExpressionKind::Literal(Literal::String { value }) => {
                assert_eq!(value, "hello %v");
            }
            _ => panic!("expected format literal as first argument"),
        }

        match &args[1].expression.kind {
            ExpressionKind::Identifier(identifier) => {
                assert_eq!(identifier.symbol.as_str(), "name");
            }
            _ => panic!("expected interpolation expression as second argument"),
        }

        match &callee.kind {
            ExpressionKind::Member { target, name, .. } => {
                assert_eq!(name.symbol.as_str(), "sprintf");
                match &target.kind {
                    ExpressionKind::Identifier(identifier) => {
                        assert_eq!(identifier.symbol.as_str(), "std");
                    }
                    _ => panic!("expected std identifier target"),
                }
            }
            _ => panic!("expected std.sprintf member call"),
        }
    }

    #[test]
    fn test_fstring_interpolation_escapes_percent_in_literal_segments() {
        let expr = parse_expr_str(r#"f"100% {value}""#);
        let ExpressionKind::Call(_, args) = &expr.kind else {
            panic!("expected call expression");
        };
        match &args[0].expression.kind {
            ExpressionKind::Literal(Literal::String { value }) => {
                assert_eq!(value, "100%% %v");
            }
            _ => panic!("expected format literal"),
        }
    }

    #[test]
    fn fstring_percent_escaping_preserves_literal_and_interpolated_segments() {
        let literal = parse_expr_str(r#"f"100% {{done}} %%""#);
        assert!(
            matches!(&literal.kind, ExpressionKind::Literal(Literal::String { value })
            if value == "100% {done} %%")
        );
        let call = parse_expr_str(r#"f"100% {first} %% {second}%""#);
        let ExpressionKind::Call(_, args) = &call.kind else {
            panic!("expected format call")
        };
        assert_eq!(args.len(), 3);
        assert!(matches!(&args[0].expression.kind,
            ExpressionKind::Literal(Literal::String { value })
            if value == "100%% %v %%%% %v%%"));
    }

    #[test]
    fn test_literal_bool() {
        let expr = parse_expr_str("true");
        assert!(matches!(
            expr.kind,
            ExpressionKind::Literal(Literal::Bool(true))
        ));
    }

    #[test]
    fn test_literal_nil() {
        let expr = parse_expr_str("nil");
        assert!(matches!(expr.kind, ExpressionKind::Literal(Literal::Nil)));
    }

    #[test]
    fn test_identifier_expr() {
        let expr = parse_expr_str("foo");
        assert!(matches!(expr.kind, ExpressionKind::Identifier(_)));
    }

    #[test]
    fn test_binary_expr_arithmetic() {
        let expr = parse_expr_str("a + b");
        assert!(matches!(expr.kind, ExpressionKind::Binary(_, _, _)));
    }

    #[test]
    fn test_binary_expr_comparison() {
        let expr = parse_expr_str("a == b");
        assert!(matches!(expr.kind, ExpressionKind::Binary(_, _, _)));
    }

    #[test]
    fn test_precedence() {
        let expr = parse_expr_str("1 + 2 * 3");
        match &expr.kind {
            ExpressionKind::Binary(op, _, rhs) => {
                assert!(matches!(op, BinaryOperator::Add));
                assert!(matches!(rhs.kind, ExpressionKind::Binary(_, _, _)));
            }
            _ => panic!("Expected binary"),
        }
    }

    #[test]
    fn test_assignment_expr() {
        let expr = parse_expr_str("a = b");
        assert!(matches!(expr.kind, ExpressionKind::Assign(_, _)));
    }

    #[test]
    fn test_range_expr() {
        let expr = parse_expr_str("1..10");
        assert!(matches!(expr.kind, ExpressionKind::Range(_, _, _)));
    }

    #[test]
    fn test_nil_coalesce_expr() {
        let expr = parse_expr_str("a ?? b");
        assert!(matches!(expr.kind, ExpressionKind::OptionalDefault(_, _)));
    }

    #[test]
    fn test_nil_coalesce_chain() {
        let expr = parse_expr_str("a ?? b ?? c");
        // Right-associative: a ?? (b ?? c)
        if let ExpressionKind::OptionalDefault(_, rhs) = &expr.kind {
            assert!(matches!(rhs.kind, ExpressionKind::OptionalDefault(_, _)));
        } else {
            panic!("Expected OptionalDefault");
        }
    }

    #[test]
    fn test_ternary_expr() {
        let expr = parse_expr_str("cond ? a : b");
        assert!(matches!(expr.kind, ExpressionKind::Ternary(_, _, _)));
    }

    #[test]
    fn test_pipe_expr() {
        let expr = parse_expr_str("a |> b |> c");
        assert!(matches!(expr.kind, ExpressionKind::Pipe(_, _)));
    }

    #[test]
    fn test_cast_expr() {
        let expr = parse_expr_str("x as int64");
        assert!(matches!(expr.kind, ExpressionKind::CastAs(_, _)));
    }

    #[test]
    fn test_try_cast_expr() {
        let expr = parse_expr_str("x as? any Printable");
        assert!(matches!(expr.kind, ExpressionKind::CastAsTry(_, _)));
    }

    #[test]
    fn test_type_is_expr() {
        let expr = parse_expr_str("x is any Printable");
        assert!(matches!(expr.kind, ExpressionKind::TypeIs(_, _)));
    }

    #[test]
    fn test_prefix_expr_not() {
        let expr = parse_expr_str("!a");
        assert!(matches!(
            &expr.kind,
            ExpressionKind::Unary(UnaryOperator::LogicalNot, _)
        ));
    }

    #[test]
    fn test_prefix_expr_neg() {
        let expr = parse_expr_str("-a");
        assert!(matches!(
            &expr.kind,
            ExpressionKind::Unary(UnaryOperator::Negate, _)
        ));
    }

    #[test]
    fn test_prefix_expr_ref() {
        let expr = parse_expr_str("&a");
        assert!(matches!(&expr.kind, ExpressionKind::Reference(_)));
    }

    #[test]
    fn test_prefix_expr_deref() {
        let expr = parse_expr_str("*a");
        assert!(matches!(&expr.kind, ExpressionKind::Dereference(_)));
    }

    #[test]
    fn test_postfix_call() {
        let expr = parse_expr_str("f()");
        assert!(matches!(expr.kind, ExpressionKind::Call(_, _)));
    }

    #[test]
    fn test_postfix_call_with_args() {
        let expr = parse_expr_str("f(a, b, c)");
        assert!(matches!(&expr.kind, ExpressionKind::Call(_, args) if args.len() == 3));
    }

    #[test]
    fn test_postfix_member() {
        let expr = parse_expr_str("a.b");
        assert!(matches!(expr.kind, ExpressionKind::Member { .. }));
    }

    #[test]
    fn test_postfix_tuple_member() {
        // Test via declaration context to avoid lexer integer literal parsing
        let decl = parse_one_decl("func foo(t: (int32, int32)) { var _ = t.0; }");
        assert!(matches!(decl.kind, DeclarationKind::Function(_)));
    }

    #[test]
    fn test_postfix_index() {
        // Test via declaration context since indexing requires subscript expressions
        let decl = parse_one_decl("func foo(a: [int32]) { var _ = a[0]; }");
        assert!(matches!(decl.kind, DeclarationKind::Function(_)));
    }

    #[test]
    fn test_postfix_optional() {
        let expr = parse_expr_str("foo");
        // Simple test - optional unwrap tested indirectly through other tests
        assert!(matches!(expr.kind, ExpressionKind::Identifier(_)));
    }

    #[test]
    fn test_tuple_expr_empty() {
        let expr = parse_expr_str("()");
        assert!(matches!(expr.kind, ExpressionKind::Tuple(_)));
    }

    #[test]
    fn test_tuple_expr() {
        let expr = parse_expr_str("(a, b, c)");
        assert!(matches!(&expr.kind, ExpressionKind::Tuple(elems) if elems.len() == 3));
    }

    #[test]
    fn test_single_element_tuple_expr() {
        let expr = parse_expr_str("(1,)");
        assert!(matches!(&expr.kind, ExpressionKind::Tuple(elems) if elems.len() == 1));
    }

    #[test]
    fn test_parenthesized_expr_no_comma() {
        let expr = parse_expr_str("(1)");
        assert!(matches!(expr.kind, ExpressionKind::Parenthesis(_)));
    }

    #[test]
    fn test_array_expr_empty() {
        let expr = parse_expr_str("[]");
        assert!(matches!(expr.kind, ExpressionKind::Array(_)));
    }

    #[test]
    fn test_array_expr() {
        let expr = parse_expr_str("[1, 2, 3]");
        assert!(matches!(&expr.kind, ExpressionKind::Array(elems) if elems.len() == 3));
    }

    #[test]
    fn test_array_repeat_expr() {
        let expr = parse_expr_str("[0; 10]");
        assert!(matches!(expr.kind, ExpressionKind::Repeat { .. }));
    }

    #[test]
    fn test_dict_expr_empty() {
        let expr = parse_expr_str("[:]");
        assert!(matches!(expr.kind, ExpressionKind::DictionaryLiteral(_)));
    }

    #[test]
    fn test_dict_expr() {
        let expr = parse_expr_str("[\"a\": 1, \"b\": 2]");
        assert!(matches!(&expr.kind, ExpressionKind::DictionaryLiteral(pairs) if pairs.len() == 2));
    }

    #[test]
    fn test_if_expr() {
        let expr = parse_expr_str("if cond { a } else { b }");
        assert!(matches!(expr.kind, ExpressionKind::If(_)));
    }

    #[test]
    fn test_match_expr() {
        let decl = parse_one_decl("func foo(x: int32) { match x { case 1 => 10; case 2 => 20; } }");
        assert!(matches!(decl.kind, DeclarationKind::Function(_)));
    }

    #[test]
    fn test_match_arm_shorthand() {
        let decl = parse_one_decl("func foo(x: int32) { match x { _ => 0; } }");
        assert!(matches!(decl.kind, DeclarationKind::Function(_)));
    }

    #[test]
    fn test_match_missing_case_recovers_following_arm_and_statement() {
        let input = "func test() {
            x := 1;
            y := match x {
                1 => 10;
                case _ => 0;
            };
            z := 2;
        }";
        let (decls, errors) = parse_decls_with_recovery(input);

        assert!(
            errors
                .iter()
                .any(|err| matches!(err.value, ParserError::ExpectedMatchArmCaseKeyword)),
            "missing-case recovery error should be reported"
        );

        let func = decls
            .into_iter()
            .find(|d| matches!(d.kind, DeclarationKind::Function(_)))
            .unwrap();

        if let DeclarationKind::Function(f) = func.kind {
            let body = f.block.unwrap();
            let let_count = body
                .statements
                .iter()
                .filter(|s| matches!(s.kind, StatementKind::Variable(_)))
                .count();
            assert_eq!(let_count, 3, "should recover later statements after match");

            let match_expr = body
                .statements
                .iter()
                .find_map(|stmt| match &stmt.kind {
                    StatementKind::Variable(local) => match local.initializer.as_ref() {
                        Some(expr) => match &expr.kind {
                            ExpressionKind::Match(match_expr) => Some(match_expr),
                            _ => None,
                        },
                        None => None,
                    },
                    _ => None,
                })
                .expect("expected match initializer");
            assert_eq!(match_expr.arms.len(), 2, "should recover later match arms");
        } else {
            panic!("Expected function");
        }
    }

    #[test]
    fn test_match_missing_case_recovers_guarded_arm() {
        let input = "func test(x: int32) {
            y := match x {
                n if n > 0 => 1;
                case _ => 0;
            };
        }";
        let (decls, errors) = parse_decls_with_recovery(input);

        assert!(
            errors
                .iter()
                .any(|err| matches!(err.value, ParserError::ExpectedMatchArmCaseKeyword)),
            "missing-case recovery error should be reported"
        );

        let func = decls
            .into_iter()
            .find(|d| matches!(d.kind, DeclarationKind::Function(_)))
            .unwrap();

        if let DeclarationKind::Function(f) = func.kind {
            let body = f.block.unwrap();
            let match_expr = body
                .statements
                .iter()
                .find_map(|stmt| match &stmt.kind {
                    StatementKind::Variable(local) => match local.initializer.as_ref() {
                        Some(expr) => match &expr.kind {
                            ExpressionKind::Match(match_expr) => Some(match_expr),
                            _ => None,
                        },
                        None => None,
                    },
                    _ => None,
                })
                .expect("expected match initializer");
            assert_eq!(match_expr.arms.len(), 2, "should recover guarded match arm");
            assert!(
                match_expr.arms[0].guard.is_some(),
                "recovered arm should preserve its guard"
            );
        } else {
            panic!("Expected function");
        }
    }

    #[test]
    fn test_closure_expr() {
        let expr = parse_expr_str("(x) => x + 1");
        assert!(matches!(expr.kind, ExpressionKind::Closure(_)));
    }

    #[test]
    fn test_closure_expr_empty() {
        let expr = parse_expr_str("() => 42");
        assert!(matches!(expr.kind, ExpressionKind::Closure(_)));
    }

    #[test]
    fn removed_move_closures_report_a_deliberate_diagnostic() {
        for source in [
            "func f() { value := move () => 42 }",
            "func f() { value := move (x: int32) -> int32 => x }",
            "func f() { value := move () async => { 42 } }",
        ] {
            let errors = parse_decls(source).unwrap_err();
            assert!(
                errors
                    .iter()
                    .any(|error| matches!(error.value, ParserError::MoveClosureRemoved)),
                "{errors:?}"
            );
        }
    }

    #[test]
    fn test_move_identifier_bit_or_is_not_move_closure() {
        let expr = parse_expr_str("move | flags");
        match &expr.kind {
            ExpressionKind::Binary(BinaryOperator::BitOr, lhs, rhs) => {
                assert!(matches!(lhs.kind, ExpressionKind::Identifier(_)));
                assert!(matches!(rhs.kind, ExpressionKind::Identifier(_)));
            }
            _ => panic!("Expected bitwise-or expression"),
        }
    }

    #[test]
    fn test_async_closure_expr_empty() {
        let expr = parse_expr_str("() async => { 42 }");
        match &expr.kind {
            ExpressionKind::Closure(closure) => assert!(closure.is_async),
            _ => panic!("Expected closure"),
        }
    }

    #[test]
    fn test_struct_literal() {
        let expr = parse_expr_str("Point { x: 1, y: 2 }");
        assert!(matches!(expr.kind, ExpressionKind::StructLiteral(_)));
    }

    #[test]
    fn test_block_expr() {
        let expr = parse_expr_str("{ x := 1; x }");
        assert!(matches!(expr.kind, ExpressionKind::Block(_)));
    }

    #[test]
    fn test_inferred_member_expr() {
        let expr = parse_expr_str(".foo");
        assert!(matches!(expr.kind, ExpressionKind::InferredMember { .. }));
    }

    // ==================== EDGE CASE TESTS ====================

    #[test]
    fn test_trailing_comma_array() {
        let expr = parse_expr_str("[1, 2, 3,]");
        assert!(matches!(&expr.kind, ExpressionKind::Array(elems) if elems.len() == 3));
    }

    #[test]
    fn test_paren_expr() {
        let expr = parse_expr_str("(a + b)");
        // Parser wraps in Parenthesis; inner is Binary
        assert!(matches!(expr.kind, ExpressionKind::Parenthesis(_)));
    }

    #[test]
    fn test_specialize_expr() {
        let expr = parse_expr_str("foo[int32]");
        assert!(matches!(expr.kind, ExpressionKind::Specialize { .. }));
    }

    #[test]
    fn specialized_calls_and_indexed_places_keep_the_complete_source_span() {
        for source in ["identity[int32](3)", "values[index]", "matrix[row][column]"] {
            let expr = parse_expr_str(source);
            assert_eq!(expr.span.start.offset, 0, "{source}");
            assert_eq!(expr.span.end.offset, source.len(), "{source}");
        }
    }

    #[test]
    fn bracket_suffix_preserves_value_and_type_interpretations() {
        let expr = parse_expr_str("values[key]");
        assert!(matches!(
            expr.kind,
            ExpressionKind::Specialize { index: Some(_), .. }
        ));
        let expr = parse_expr_str("values[key + 1]");
        assert!(matches!(expr.kind, ExpressionKind::Index { .. }));
        let expr = parse_expr_str("values[&key]");
        assert!(matches!(
            expr.kind,
            ExpressionKind::Specialize { index: Some(_), .. }
        ));
        let expr = parse_expr_str("factory[int32, 3]");
        assert!(matches!(
            expr.kind,
            ExpressionKind::Specialize { index: Some(ref index), .. } if index.len() == 2
        ));
    }

    #[test]
    fn g40_generic_wildcards_do_not_leak_speculative_index_errors() {
        for source in [
            "group[int32, (), _]",
            "group[_]",
            "value.method[int32, (), _]",
        ] {
            let expression = parse_expr_str(source);
            assert!(
                matches!(
                    expression.kind,
                    ExpressionKind::Specialize { index: None, .. }
                ),
                "{source}"
            );
        }
        let mut parser = parser("values[_ + 1]");
        parser
            .parse_expression()
            .expect("recover invalid index expression");
        let errors = parser.errors;
        assert!(
            errors
                .iter()
                .any(|error| matches!(error.value, ParserError::DisallowedWildcardExpression)),
            "{errors:#?}"
        );
    }

    #[test]
    fn bracket_suffix_supports_nested_and_callable_elements() {
        let expr = parse_expr_str("matrix[row][column]");
        let ExpressionKind::Specialize {
            target,
            index: Some(_),
            ..
        } = expr.kind
        else {
            panic!("outer subscript")
        };
        assert!(matches!(
            target.kind,
            ExpressionKind::Specialize { index: Some(_), .. }
        ));
        let expr = parse_expr_str("callbacks[index]()");
        let ExpressionKind::Call(callee, _) = expr.kind else {
            panic!("element call")
        };
        assert!(matches!(
            callee.kind,
            ExpressionKind::Specialize { index: Some(_), .. }
        ));
    }

    #[test]
    fn test_complex_chain() {
        // Test complex chains in declaration context
        let decl = parse_one_decl("func foo(a: Foo?) { var _ = a?.b.c(); }");
        assert!(matches!(decl.kind, DeclarationKind::Function(_)));
    }

    // ==================== LITERAL TESTS (EXTENDED) ====================

    #[test]
    fn test_literal_string_multiline() {
        let decl = parse_one_decl(r#"const S: string = "hello\nworld""#);
        assert!(matches!(decl.kind, DeclarationKind::Constant(_)));
    }

    #[test]
    fn test_literal_rune() {
        let expr = parse_expr_str("'a'");
        assert!(matches!(
            &expr.kind,
            ExpressionKind::Literal(Literal::Rune { .. })
        ));
    }

    #[test]
    fn test_literal_rune_escape() {
        let expr = parse_expr_str(r"'\n'");
        assert!(matches!(
            &expr.kind,
            ExpressionKind::Literal(Literal::Rune { .. })
        ));
    }

    #[test]
    fn test_literal_integer_hex() {
        let expr = parse_expr_str("0xFF");
        assert!(matches!(
            &expr.kind,
            ExpressionKind::Literal(Literal::Integer {
                base: Base::Hexadecimal,
                ..
            })
        ));
    }

    #[test]
    fn test_literal_integer_binary() {
        let expr = parse_expr_str("0b1010");
        assert!(matches!(
            &expr.kind,
            ExpressionKind::Literal(Literal::Integer {
                base: Base::Binary,
                ..
            })
        ));
    }

    #[test]
    fn test_literal_integer_octal() {
        let expr = parse_expr_str("0o77");
        assert!(matches!(
            &expr.kind,
            ExpressionKind::Literal(Literal::Integer {
                base: Base::Octal,
                ..
            })
        ));
    }

    #[test]
    fn test_literal_integer_with_underscores() {
        let expr = parse_expr_str("1_000_000");
        assert!(matches!(
            &expr.kind,
            ExpressionKind::Literal(Literal::Integer { .. })
        ));
    }

    #[test]
    fn test_literal_integer_with_type_suffix() {
        let expr = parse_expr_str("1_u32");
        assert!(matches!(
            &expr.kind,
            ExpressionKind::Literal(Literal::Integer {
                suffix: Some(IntegerTypeSuffix::U32),
                ..
            })
        ));
    }

    #[test]
    fn test_literal_float_exponent() {
        let expr = parse_expr_str("1.5e10");
        assert!(matches!(
            &expr.kind,
            ExpressionKind::Literal(Literal::Float { .. })
        ));
    }

    #[test]
    fn test_literal_float_negative_exponent() {
        let expr = parse_expr_str("1.5e-10");
        assert!(matches!(
            &expr.kind,
            ExpressionKind::Literal(Literal::Float { .. })
        ));
    }

    // ==================== TYPE TESTS (EXTENDED) ====================

    #[test]
    fn test_nested_pointer_type() {
        let ty = parse_type_str("**int32");
        match &ty.kind {
            TypeKind::Pointer(inner, _) => assert!(matches!(inner.kind, TypeKind::Pointer(_, _))),
            _ => panic!("Expected nested pointer"),
        }
    }

    #[test]
    fn test_nested_reference_type() {
        let ty = parse_type_str("&&int32");
        match &ty.kind {
            TypeKind::Reference(inner) => {
                assert!(matches!(inner.kind, TypeKind::Reference(_)))
            }
            _ => panic!("Expected nested reference"),
        }
    }

    #[test]
    fn test_pointer_to_reference() {
        let ty = parse_type_str("*&int32");
        match &ty.kind {
            TypeKind::Pointer(inner, _) => assert!(matches!(inner.kind, TypeKind::Reference(_))),
            _ => panic!("Expected pointer to reference"),
        }
    }

    #[test]
    fn test_reference_to_pointer() {
        let ty = parse_type_str("&*int32");
        match &ty.kind {
            TypeKind::Reference(inner) => assert!(matches!(inner.kind, TypeKind::Pointer(_, _))),
            _ => panic!("Expected reference to pointer"),
        }
    }

    #[test]
    fn test_const_reference_type_rejected() {
        let errors =
            parse_decls("func f(_ value: &const int32) {}").expect_err("obsolete borrow spelling");
        assert!(
            errors
                .iter()
                .any(|e| matches!(e.value, ParserError::ReferenceConstModifier))
        );
    }

    #[test]
    fn test_infer_type() {
        let ty = parse_type_str("_");
        assert!(matches!(ty.kind, TypeKind::Infer));
    }

    #[test]
    fn test_paren_type() {
        let ty = parse_type_str("(int32)");
        assert!(matches!(ty.kind, TypeKind::Parenthesis(_)));
    }

    #[test]
    fn test_optional_pointer() {
        let ty = parse_type_str("(*int32)?");
        assert!(matches!(ty.kind, TypeKind::Optional(_)));
    }

    #[test]
    fn test_list_of_optionals() {
        let ty = parse_type_str("[int32?]");
        assert!(matches!(ty.kind, TypeKind::List(_)));
    }

    #[test]
    fn test_function_type_multiple_params() {
        let ty = parse_type_str("(int32, string, bool) -> int32");
        match &ty.kind {
            TypeKind::Function { inputs, .. } => assert_eq!(inputs.len(), 3),
            _ => panic!("Expected function type"),
        }
    }

    #[test]
    fn test_multi_generic_type() {
        let ty = parse_type_str("Map[string, [int32]]");
        assert!(matches!(ty.kind, TypeKind::Nominal(_)));
    }

    #[test]
    fn test_existential_multiple_bounds() {
        let ty = parse_type_str("any Hashable & Equatable");
        assert!(matches!(ty.kind, TypeKind::BoxedExistential { .. }));
    }

    #[test]
    fn test_existential_multiple_generic_bounds() {
        let ty = parse_type_str("any Slot[int32] & Slot[string]");
        assert!(
            matches!(&ty.kind, TypeKind::BoxedExistential { interfaces } if interfaces.len() == 2)
        );
    }

    // ==================== PATTERN TESTS (EXTENDED) ====================

    #[test]
    fn test_rest_pattern() {
        let pattern = parse_pattern_str("(a, ..)");
        match &pattern.kind {
            PatternKind::Tuple(pats, _) => assert!(matches!(pats[1].kind, PatternKind::Rest)),
            _ => panic!("Expected tuple with rest"),
        }
    }

    #[test]
    fn test_or_pattern() {
        let decl = parse_one_decl("func foo(x: int32) { match x { case 1 | 2 | 3 => 0; } }");
        assert!(matches!(decl.kind, DeclarationKind::Function(_)));
    }

    #[test]
    fn test_literal_pattern_integer() {
        let decl = parse_one_decl("func foo(x: int32) { match x { case 42 => 0; } }");
        assert!(matches!(decl.kind, DeclarationKind::Function(_)));
    }

    #[test]
    fn test_literal_pattern_string() {
        let decl = parse_one_decl(r#"func foo(x: string) { match x { case "hello" => 0; } }"#);
        assert!(matches!(decl.kind, DeclarationKind::Function(_)));
    }

    #[test]
    fn test_path_pattern_qualified() {
        let decl =
            parse_one_decl("func foo(x: Option[int32]) { match x { case Option::some(v) => v; } }");
        assert!(matches!(decl.kind, DeclarationKind::Function(_)));
    }

    #[test]
    fn test_path_pattern_inferred() {
        let decl = parse_one_decl(
            "func foo(x: Option[int32]) { match x { case .some(v) => v; case .none => 0; } }",
        );
        assert!(matches!(decl.kind, DeclarationKind::Function(_)));
    }

    #[test]
    fn test_const_reference_pattern_rejected() {
        let errors = parse_decls("func f() { match value { case &const x => x; } }")
            .expect_err("obsolete borrow spelling");
        assert!(
            errors
                .iter()
                .any(|e| matches!(e.value, ParserError::ReferenceConstModifier))
        );
    }

    // ==================== STATEMENT TESTS (EXTENDED) ====================

    #[test]
    fn test_return_with_value() {
        let decl = parse_one_decl("func foo() -> int32 { return 42 }");
        assert!(matches!(decl.kind, DeclarationKind::Function(_)));
    }

    #[test]
    fn test_return_without_value() {
        let decl = parse_one_decl("func foo() { return }");
        assert!(matches!(decl.kind, DeclarationKind::Function(_)));
    }

    #[test]
    fn test_break_with_label() {
        let decl = parse_one_decl("func foo() { outer: loop { break outer } }");
        assert!(matches!(decl.kind, DeclarationKind::Function(_)));
    }

    #[test]
    fn test_continue_with_label() {
        let decl = parse_one_decl("func foo() { outer: loop { inner: loop { continue outer } } }");
        assert!(matches!(decl.kind, DeclarationKind::Function(_)));
    }

    #[test]
    fn test_labeled_while() {
        let decl = parse_one_decl("func foo() { outer: while true { break outer } }");
        assert!(matches!(decl.kind, DeclarationKind::Function(_)));
    }

    #[test]
    fn test_label_on_non_loop_statement_is_preserved_as_warning() {
        let parser = parser("func foo() { misplaced: var x = 1 }");

        let (_decls, _module_decls, warnings) = parser.parse().expect("Parse failed");

        assert_eq!(warnings.len(), 1);
        assert!(matches!(warnings[0].value, ParserError::DisallowedLabel));
    }

    #[test]
    fn test_variable_let() {
        let decl = parse_one_decl("func foo() { x := 1 }");
        assert!(matches!(decl.kind, DeclarationKind::Function(_)));
    }

    #[test]
    fn test_variable_var() {
        let decl = parse_one_decl("func foo() { var x = 1; x = 2 }");
        assert!(matches!(decl.kind, DeclarationKind::Function(_)));
    }

    #[test]
    fn test_variable_with_type() {
        let decl = parse_one_decl("func foo() { var x: int32 = 1 }");
        assert!(matches!(decl.kind, DeclarationKind::Function(_)));
    }

    #[test]
    fn test_for_with_where() {
        let decl = parse_one_decl("func foo(xs: [int32]) { for x in xs where x > 0 { break } }");
        assert!(matches!(decl.kind, DeclarationKind::Function(_)));
    }

    #[test]
    fn test_for_await_with_where() {
        let decl = parse_one_decl(
            "func foo(xs: [int32]) async { for await x in xs where x > 0 { break } }",
        );
        assert!(matches!(decl.kind, DeclarationKind::Function(_)));
    }

    // ==================== DECLARATION TESTS (EXTENDED) ====================

    #[test]
    fn test_constant_declaration() {
        let decl = parse_one_decl("const PI: float64 = 3.14159");
        assert!(matches!(decl.kind, DeclarationKind::Constant(_)));
    }

    #[test]
    fn test_static_variable_declaration_top_level() {
        let decl = parse_one_decl("static var GLOBAL: int32 = 100");
        assert!(matches!(decl.kind, DeclarationKind::StaticVariable(_)));
    }

    #[test]
    fn test_static_variable_declaration_namespace() {
        let decl = parse_one_decl("namespace Config { static var COUNT: int32 = 0; }");
        match &decl.kind {
            DeclarationKind::Namespace(namespace) => {
                assert!(matches!(
                    namespace.declarations[0].kind,
                    NamespaceDeclarationKind::StaticVariable(_)
                ));
            }
            _ => panic!("Expected namespace declaration"),
        }
    }

    #[test]
    fn test_top_level_variable_requires_static() {
        let errors = parse_decls("var GLOBAL: int32 = 100").expect_err("expected parse failure");
        assert!(
            errors
                .iter()
                .any(|err| matches!(err.value, ParserError::TopLevelVariableMustBeStatic))
        );
    }

    #[test]
    fn test_static_variable_missing_type() {
        let errors = parse_decls("static var GLOBAL = 100").expect_err("expected parse failure");
        assert!(
            errors
                .iter()
                .any(|err| matches!(err.value, ParserError::MissingStaticTypeAnnotation))
        );
    }

    #[test]
    fn test_static_variable_missing_initializer() {
        let errors = parse_decls("static var GLOBAL: int32").expect_err("expected parse failure");
        assert!(
            errors
                .iter()
                .any(|err| matches!(err.value, ParserError::MissingStaticInitializer))
        );
    }

    #[test]
    fn test_public_visibility() {
        let decl = parse_one_decl("public struct Foo { x: int32; }");
        assert_eq!(decl.visibility.level, VisibilityLevel::Public);
    }

    #[test]
    fn internal_visibility_applies_to_declarations_and_stored_fields() {
        let decl = parse_one_decl("internal struct State { internal value: int32; }");
        assert_eq!(decl.visibility.level, VisibilityLevel::Internal);
        let DeclarationKind::Struct(definition) = decl.kind else {
            panic!("expected struct");
        };
        assert_eq!(
            definition.fields[0].visibility.level,
            VisibilityLevel::Internal
        );
    }

    #[test]
    fn test_private_visibility() {
        let decl = parse_one_decl("private func secret() { }");
        assert_eq!(decl.visibility.level, VisibilityLevel::Private);
    }

    #[test]
    fn test_attribute_on_declaration() {
        let decl = parse_one_decl("@inline func foo() { }");
        assert!(!decl.attributes.is_empty());
    }

    #[test]
    fn test_function_default_param() {
        let decl = parse_one_decl("func greet(name: string = \"World\") { }");
        match &decl.kind {
            DeclarationKind::Function(f) => {
                assert!(f.signature.prototype.inputs[0].default_value.is_some());
            }
            _ => panic!("Expected function"),
        }
    }

    #[test]
    fn test_function_variadic_param() {
        let decl = parse_one_decl("func sum(nums: int32...) { }");
        match &decl.kind {
            DeclarationKind::Function(f) => {
                assert!(f.signature.prototype.inputs[0].is_variadic);
            }
            _ => panic!("Expected function"),
        }
    }

    #[test]
    fn test_function_labeled_param() {
        let decl = parse_one_decl("func move(to destination: Point) { }");
        match &decl.kind {
            DeclarationKind::Function(f) => {
                assert!(f.signature.prototype.inputs[0].label.is_some());
            }
            _ => panic!("Expected function"),
        }
    }

    #[test]
    fn test_function_implicit_self() {
        let decl = parse_one_decl("interface Foo { func bar(); }");
        assert!(matches!(decl.kind, DeclarationKind::Interface(_)));
    }

    #[test]
    fn test_function_const_self_param() {
        let errors = parse_decls("interface Foo { func value(&const self) -> int32; }")
            .expect_err("obsolete borrow spelling");
        assert!(
            errors
                .iter()
                .any(|e| matches!(e.value, ParserError::ReferenceConstModifier))
        );
    }

    #[test]
    fn test_enum_discriminant() {
        let decl = parse_one_decl("enum Status { case ok = 0, err = 1; }");
        assert!(matches!(decl.kind, DeclarationKind::Enum(_)));
    }

    #[test]
    fn test_struct_with_visibility_fields() {
        let decl = parse_one_decl("struct Foo { public x: int32; private y: int32; }");
        assert!(matches!(&decl.kind, DeclarationKind::Struct(s) if s.fields.len() == 2));
    }

    #[test]
    fn test_import_with_alias() {
        let decl = parse_one_decl("import std::io as sio");
        assert!(matches!(decl.kind, DeclarationKind::Import(_)));
    }

    #[test]
    fn test_import_glob() {
        let decl = parse_one_decl("import std::io::*");
        match &decl.kind {
            DeclarationKind::Import(tree) => assert!(matches!(tree.kind, UseTreeKind::Glob)),
            _ => panic!("Expected import"),
        }
    }

    #[test]
    fn test_export_declaration() {
        let decl = parse_one_decl("export std::io::File");
        assert!(matches!(decl.kind, DeclarationKind::Export(_)));
    }

    #[test]
    fn test_type_alias_with_bounds() {
        let decl = parse_one_decl("type Key: Hashable");
        match &decl.kind {
            DeclarationKind::TypeAlias(ta) => assert!(ta.bounds.is_some()),
            _ => panic!("Expected type alias"),
        }
    }

    #[test]
    fn test_interface_associated_type() {
        let decl = parse_one_decl("interface Container { type Item; }");
        assert!(matches!(decl.kind, DeclarationKind::Interface(_)));
    }

    #[test]
    fn test_interface_associated_const() {
        let decl = parse_one_decl("interface Named { const NAME: string; }");
        assert!(matches!(decl.kind, DeclarationKind::Interface(_)));
    }

    #[test]
    fn test_multiple_type_parameters() {
        let decl = parse_one_decl("struct Pair[A, B] { first: A; second: B; }");
        match &decl.kind {
            DeclarationKind::Struct(s) => {
                assert_eq!(
                    s.generics
                        .type_parameters
                        .as_ref()
                        .unwrap()
                        .parameters
                        .len(),
                    2
                );
            }
            _ => panic!("Expected struct"),
        }
    }

    #[test]
    fn test_where_clause_multiple() {
        let decl = parse_one_decl("func foo[K, V]() where K: Hashable, V: Equatable { }");
        match &decl.kind {
            DeclarationKind::Function(f) => {
                let wc = f.generics.where_clause.as_ref().unwrap();
                assert_eq!(wc.requirements.len(), 2);
            }
            _ => panic!("Expected function"),
        }
    }

    #[test]
    fn test_where_same_type() {
        let decl = parse_one_decl("func foo[T]() where T::Item == int32 { }");
        match &decl.kind {
            DeclarationKind::Function(f) => assert!(f.generics.where_clause.is_some()),
            _ => panic!("Expected function"),
        }
    }

    // ==================== EXPRESSION TESTS (EXTENDED) ====================

    #[test]
    fn test_binary_logical_and() {
        let expr = parse_expr_str("a && b");
        assert!(matches!(
            &expr.kind,
            ExpressionKind::Binary(BinaryOperator::BoolAnd, _, _)
        ));
    }

    #[test]
    fn test_binary_logical_or() {
        let expr = parse_expr_str("a || b");
        assert!(matches!(
            &expr.kind,
            ExpressionKind::Binary(BinaryOperator::BoolOr, _, _)
        ));
    }

    #[test]
    fn test_binary_bitwise_and() {
        let expr = parse_expr_str("a & b");
        assert!(matches!(
            &expr.kind,
            ExpressionKind::Binary(BinaryOperator::BitAnd, _, _)
        ));
    }

    #[test]
    fn test_binary_bitwise_or() {
        let expr = parse_expr_str("a | b");
        assert!(matches!(
            &expr.kind,
            ExpressionKind::Binary(BinaryOperator::BitOr, _, _)
        ));
    }

    #[test]
    fn test_binary_bitwise_xor() {
        let expr = parse_expr_str("a ^ b");
        assert!(matches!(
            &expr.kind,
            ExpressionKind::Binary(BinaryOperator::BitXor, _, _)
        ));
    }

    #[test]
    fn test_binary_shift_left() {
        let expr = parse_expr_str("a << b");
        assert!(matches!(
            &expr.kind,
            ExpressionKind::Binary(BinaryOperator::BitShl, _, _)
        ));
    }

    #[test]
    fn test_binary_shift_right() {
        let expr = parse_expr_str("a >> b");
        assert!(matches!(
            &expr.kind,
            ExpressionKind::Binary(BinaryOperator::BitShr, _, _)
        ));
    }

    #[test]
    fn test_binary_less_than() {
        let expr = parse_expr_str("a < b");
        assert!(matches!(
            &expr.kind,
            ExpressionKind::Binary(BinaryOperator::Lt, _, _)
        ));
    }

    #[test]
    fn test_binary_greater_equal() {
        let expr = parse_expr_str("a >= b");
        assert!(matches!(
            &expr.kind,
            ExpressionKind::Binary(BinaryOperator::Geq, _, _)
        ));
    }

    #[test]
    fn test_binary_not_equal() {
        let expr = parse_expr_str("a != b");
        assert!(matches!(
            &expr.kind,
            ExpressionKind::Binary(BinaryOperator::Neq, _, _)
        ));
    }

    #[test]
    fn test_compound_assignment_add() {
        let expr = parse_expr_str("a += 1");
        assert!(matches!(
            expr.kind,
            ExpressionKind::AssignOp(BinaryOperator::Add, _, _)
        ));
    }

    #[test]
    fn test_compound_assignment_sub() {
        let expr = parse_expr_str("a -= 1");
        assert!(matches!(
            expr.kind,
            ExpressionKind::AssignOp(BinaryOperator::Sub, _, _)
        ));
    }

    #[test]
    fn test_compound_assignment_bit_and() {
        let expr = parse_expr_str("a &= b");
        assert!(matches!(
            expr.kind,
            ExpressionKind::AssignOp(BinaryOperator::BitAnd, _, _)
        ));
    }

    #[test]
    fn test_prefix_bitwise_not() {
        let expr = parse_expr_str("~a");
        assert!(matches!(
            &expr.kind,
            ExpressionKind::Unary(UnaryOperator::BitwiseNot, _)
        ));
    }

    #[test]
    fn test_prefix_const_ref_rejected() {
        let errors = parse_decls("func f() { reference := &const value; }")
            .expect_err("obsolete borrow spelling");
        assert!(
            errors
                .iter()
                .any(|e| matches!(e.value, ParserError::ReferenceConstModifier))
        );
    }

    #[test]
    fn test_range_inclusive() {
        let expr = parse_expr_str("1..=10");
        assert!(matches!(&expr.kind, ExpressionKind::Range(_, _, true)));
    }

    #[test]
    fn test_range_exclusive() {
        let expr = parse_expr_str("1..10");
        assert!(matches!(&expr.kind, ExpressionKind::Range(_, _, false)));
    }

    #[test]
    fn test_if_else_chain() {
        let expr = parse_expr_str("if a { 1 } else if b { 2 } else { 3 }");
        assert!(matches!(expr.kind, ExpressionKind::If(_)));
    }

    #[test]
    fn test_if_arrow_syntax() {
        // Arrow syntax for if conditions
        let decl = parse_one_decl("func foo(x: bool) -> int32 { if x { 1 } else { 0 } }");
        assert!(matches!(decl.kind, DeclarationKind::Function(_)));
    }

    #[test]
    fn test_closure_typed_params() {
        let expr = parse_expr_str("(x: int32, y: int32) => x + y");
        assert!(matches!(expr.kind, ExpressionKind::Closure(_)));
    }

    #[test]
    fn test_closure_typed_param_with_generic_type() {
        let expr = parse_expr_str("(group: std::task::TaskGroup[int32]) async => { return 0 }");
        let ExpressionKind::Closure(closure) = &expr.kind else {
            panic!("Expected closure");
        };
        assert!(closure.is_async);
        assert_eq!(closure.signature.prototype.inputs.len(), 1);
        let param_ty = &closure.signature.prototype.inputs[0].annotated_type;
        let TypeKind::Nominal(path) = &param_ty.kind else {
            panic!("Expected nominal type");
        };
        assert_eq!(path.segments.len(), 3);
        assert!(path.segments[2].arguments.is_some());
    }

    #[test]
    fn test_closure_with_return_type() {
        let expr = parse_expr_str("(x: int32) -> int32 => x * 2");
        assert!(matches!(expr.kind, ExpressionKind::Closure(_)));
    }

    #[test]
    fn test_closure_block_body() {
        let expr = parse_expr_str("(x) => { y := x; y }");
        assert!(matches!(expr.kind, ExpressionKind::Closure(_)));
    }

    #[test]
    fn test_async_closure_with_return_type() {
        let expr = parse_expr_str("(x: int32) -> int32 async => { x * 2 }");
        match &expr.kind {
            ExpressionKind::Closure(closure) => {
                assert!(closure.is_async);
                assert!(matches!(closure.body.kind, ExpressionKind::Block(_)));
            }
            _ => panic!("Expected closure"),
        }
    }

    #[test]
    fn test_async_closure_prefix_syntax_is_rejected() {
        let errors = parse_expr_err("async () => {}");
        assert!(
            !errors.is_empty(),
            "expected parse error for `async () => {{}}`"
        );
    }

    #[test]
    fn test_struct_literal_shorthand() {
        let expr = parse_expr_str("Point { x, y }");
        match &expr.kind {
            ExpressionKind::StructLiteral(s) => {
                assert!(s.fields[0].is_shorthand);
            }
            _ => panic!("Expected struct literal"),
        }
    }

    #[test]
    fn wildcard_expression_is_recovered_with_a_diagnostic() {
        let mut parser = parser("_");
        let expr = parser
            .parse_expression()
            .expect("recover wildcard expression");
        assert!(matches!(expr.kind, ExpressionKind::Wildcard));
        assert_eq!(parser.errors.len(), 1);
        assert!(matches!(
            parser.errors[0].value,
            ParserError::DisallowedWildcardExpression
        ));
    }

    #[test]
    fn test_optional_chain_member() {
        let decl = parse_one_decl("func foo(a: Foo?) { var _ = a?.bar }");
        assert!(matches!(decl.kind, DeclarationKind::Function(_)));
    }

    #[test]
    fn test_optional_chain_call() {
        let decl = parse_one_decl("func foo(a: Foo?) { var _ = a?.method() }");
        assert!(matches!(decl.kind, DeclarationKind::Function(_)));
    }

    #[test]
    fn test_case_binding_condition() {
        let decl = parse_one_decl("func foo(x: Option[int32]) { if case .some(v) = x { } }");
        assert!(matches!(decl.kind, DeclarationKind::Function(_)));
    }

    #[test]
    fn test_let_binding_condition() {
        let decl = parse_one_decl("func foo(x: int32?) { if var val = x { } }");
        assert!(matches!(decl.kind, DeclarationKind::Function(_)));
    }

    #[test]
    fn test_match_guard() {
        let decl =
            parse_one_decl("func foo(x: int32) { match x { case n if n > 0 => 1; case _ => 0; } }");
        assert!(matches!(decl.kind, DeclarationKind::Function(_)));
    }

    #[test]
    fn test_call_with_labeled_args() {
        let expr = parse_expr_str("foo(a: 1, b: 2)");
        match &expr.kind {
            ExpressionKind::Call(_, args) => {
                assert!(args[0].label.is_some());
                assert!(args[1].label.is_some());
            }
            _ => panic!("Expected call"),
        }
    }

    #[test]
    fn test_multiple_postfix_ops() {
        // Test member chaining instead of double indexing
        let decl = parse_one_decl("func foo(a: Foo) { var _ = a.bar.baz }");
        assert!(matches!(decl.kind, DeclarationKind::Function(_)));
    }

    #[test]
    fn test_trailing_comma_function_params() {
        let decl = parse_one_decl("func foo(a: int32, b: int32,) { }");
        assert!(matches!(decl.kind, DeclarationKind::Function(_)));
    }

    #[test]
    fn test_trailing_comma_tuple_type() {
        let ty = parse_type_str("(int32, string,)");
        assert!(matches!(ty.kind, TypeKind::Tuple(_)));
    }

    #[test]
    fn test_trailing_comma_call() {
        let expr = parse_expr_str("foo(1, 2, 3,)");
        assert!(matches!(expr.kind, ExpressionKind::Call(_, _)));
    }

    #[test]
    fn test_trailing_comma_generic_args() {
        let ty = parse_type_str("Map[string, int32,]");
        assert!(matches!(ty.kind, TypeKind::Nominal(_)));
    }

    #[test]
    fn test_optional_chaining_simple() {
        // a?.b should parse as OptionalEvaluation(Member(OptionalUnwrap(a), "b"))
        let expr = parse_expr_str("a?.b");
        match &expr.kind {
            ExpressionKind::OptionalEvaluation(inner) => match &inner.kind {
                ExpressionKind::Member { target, name, .. } => {
                    assert_eq!(name.symbol.as_str(), "b");
                    assert!(matches!(target.kind, ExpressionKind::OptionalUnwrap(_)));
                }
                _ => panic!("Expected Member inside OptionalEvaluation"),
            },
            _ => panic!("Expected OptionalEvaluation"),
        }
    }

    #[test]
    fn test_optional_chaining_nested() {
        // a?.b?.c should have the structure:
        // OptionalEvaluation(Member(OptionalUnwrap(Member(OptionalUnwrap(a), "b")), "c"))
        let expr = parse_expr_str("a?.b?.c");
        match &expr.kind {
            ExpressionKind::OptionalEvaluation(inner) => {
                // Outer: Member(.., "c")
                match &inner.kind {
                    ExpressionKind::Member {
                        target: outer_target,
                        name: outer_name,
                        ..
                    } => {
                        assert_eq!(outer_name.symbol.as_str(), "c");
                        // Should be OptionalUnwrap(Member(..))
                        match &outer_target.kind {
                            ExpressionKind::OptionalUnwrap(middle) => {
                                // Inner: Member(.., "b")
                                match &middle.kind {
                                    ExpressionKind::Member {
                                        target: inner_target,
                                        name: inner_name,
                                        ..
                                    } => {
                                        assert_eq!(inner_name.symbol.as_str(), "b");
                                        // Should be OptionalUnwrap(a)
                                        assert!(matches!(
                                            inner_target.kind,
                                            ExpressionKind::OptionalUnwrap(_)
                                        ));
                                    }
                                    _ => panic!("Expected Member for inner chain"),
                                }
                            }
                            _ => panic!("Expected OptionalUnwrap"),
                        }
                    }
                    _ => panic!("Expected Member at top level"),
                }
            }
            _ => panic!("Expected OptionalEvaluation"),
        }
    }

    #[test]
    fn test_propagate_simple() {
        let expr = parse_expr_str("a!");
        assert!(matches!(expr.kind, ExpressionKind::Propagate(_)));
    }

    #[test]
    fn test_propagate_after_call() {
        let expr = parse_expr_str("foo()!");
        match &expr.kind {
            ExpressionKind::Propagate(inner) => {
                assert!(matches!(inner.kind, ExpressionKind::Call(_, _)));
            }
            _ => panic!("Expected Propagate"),
        }
    }

    #[test]
    fn test_propagate_nested() {
        let expr = parse_expr_str("opt!!");
        match &expr.kind {
            ExpressionKind::Propagate(inner) => {
                assert!(matches!(inner.kind, ExpressionKind::Propagate(_)));
            }
            _ => panic!("Expected Propagate"),
        }
    }

    #[test]
    fn test_propagate_after_parenthesized_await() {
        let expr = parse_expr_str("(await task.result())!");
        match &expr.kind {
            ExpressionKind::Propagate(inner) => {
                assert!(matches!(inner.kind, ExpressionKind::Parenthesis(_)));
            }
            _ => panic!("Expected Propagate"),
        }
    }

    #[test]
    fn test_extern_block_parsing() {
        let input = r#"
        extern "taro_rt" {
            func __rt__print(_ s: string)
            func __rt__eprint(_ s: string)
        }
        "#;
        // This should parse correctly with ASI providing semicolons after signatures
        let _ = parse_one_decl(input);
    }

    #[test]
    fn test_blocking_extern_function_parsing() {
        let input =
            r#"extern "blocking" func read(_ fd: int32, _ ptr: *mut uint8, _ len: usize) -> isize"#;
        let decl = parse_one_decl(input);
        let DeclarationKind::Function(function) = &decl.kind else {
            panic!("expected blocking extern function");
        };
        assert_eq!(
            function
                .abi
                .as_ref()
                .expect("expected blocking ABI")
                .as_str(),
            "blocking"
        );
    }

    #[test]
    fn test_extern_standalone_function() {
        let input = r#"extern "C" func malloc(size: int32) -> *u8;"#;
        let decl = parse_one_decl(input);
        match &decl.kind {
            DeclarationKind::Function(func) => {
                assert_eq!(func.abi.as_ref().expect("Expected ABI").as_str(), "C");
                assert_eq!(decl.identifier.symbol.as_str(), "malloc");
            }
            _ => panic!("Expected function"),
        }
    }

    #[test]
    fn test_unsafe_function_modifier() {
        let decl = parse_one_decl("public unsafe func foo() {}");
        match &decl.kind {
            DeclarationKind::Function(func) => {
                assert!(func.is_unsafe);
                assert_eq!(decl.identifier.symbol.as_str(), "foo");
            }
            _ => panic!("Expected function"),
        }
    }

    #[test]
    fn test_extern_unsafe_standalone_function() {
        let input = r#"extern "C" unsafe func read(ptr: *const uint8) -> uint8;"#;
        let decl = parse_one_decl(input);
        match &decl.kind {
            DeclarationKind::Function(func) => {
                assert!(func.is_unsafe);
                assert_eq!(func.abi.as_ref().expect("Expected ABI").as_str(), "C");
                assert_eq!(decl.identifier.symbol.as_str(), "read");
            }
            _ => panic!("Expected function"),
        }
    }

    #[test]
    fn test_unsafe_block_statement_still_parses() {
        let decl = parse_one_decl("func foo() { unsafe { bar() } }");
        match &decl.kind {
            DeclarationKind::Function(func) => {
                assert!(func.block.is_some());
            }
            _ => panic!("Expected function"),
        }
    }

    #[test]
    fn native_subscript_bodies_and_multi_index_overloads_parse() {
        for source in [
            "extend Matrix { subscript(row: usize, column: usize) -> Element { get { self.read(row, column) } set(value) { self.write(row, column, value) } } }",
            "extend &Buffer { subscript(index: usize) -> Element { address { self.at(index) } } subscript(range: Range[usize]) -> Buffer { get { self.copy(range) } } }",
            "extend Child { final override subscript(index: usize) -> Element { get { self.read(index) } } }",
        ] {
            assert!(parse_decls(source).is_ok(), "{source}");
        }
    }

    #[test]
    fn native_subscript_interface_capabilities_parse() {
        for capability in ["get", "get set", "address", "get set address"] {
            let source = format!(
                "interface Readable[Key] {{ type Element; subscript(key: Key) -> Self::Element {{ {capability} }} }}"
            );
            assert!(parse_decls(&source).is_ok(), "{source}");
        }
    }

    #[test]
    fn native_subscripts_reject_duplicate_and_invalid_accessors() {
        for accessors in [
            "get { 1 } get { 2 }",
            "address { self.at(index) } address { self.at(index) }",
            "get { 1 } set(value) {} set(other) {}",
            "set(value) {}",
            "get(self) { 1 }",
            "set(value: Element) {} get { 1 }",
            "get async { 1 }",
            "address(value) { self.at(index) }",
            "unknown { 1 }",
            "",
        ] {
            let source =
                format!("extend Buffer {{ subscript(index: usize) -> Element {{ {accessors} }} }}");
            assert!(parse_decls(&source).is_err(), "accepted {source}");
        }
    }

    #[test]
    fn native_subscript_accessors_preserve_inline_policy() {
        for policy in ["inline", "noinline"] {
            for accessors in [
                "address { self.at(index) }",
                "get { self.read(index) } set(value) { self.write(index, value) }",
            ] {
                let declaration = parse_one_decl(&format!(
                    "extend Buffer {{ @{policy} subscript(index: usize) -> Element {{ {accessors} }} }}"
                ));
                let DeclarationKind::Impl(block) = declaration.kind else {
                    panic!("extend")
                };
                for accessor in &block.declarations[1..] {
                    assert_eq!(accessor.attributes.len(), 1);
                    assert_eq!(accessor.attributes[0].identifier.symbol.as_str(), policy);
                }
            }
        }
    }

    #[test]
    fn native_subscript_address_defaults_have_fresh_syntax_and_implicit_receivers() {
        let declaration = parse_one_decl(
            "extend &Buffer { subscript(value: Map[Key, [Element; 2]]) -> Element { address { self.at(value) } } }",
        );
        let DeclarationKind::Impl(block) = &declaration.kind else {
            panic!("extend")
        };
        let AssociatedDeclarationKind::Subscript(subscript) = &block.declarations[0].kind else {
            panic!("subscript")
        };
        assert_eq!(block.declarations.len(), 4);
        assert_eq!(subscript.getter_id, Some(block.declarations[1].id));
        assert_eq!(subscript.setter_id, Some(block.declarations[2].id));
        assert_eq!(subscript.address_id, Some(block.declarations[3].id));
        for accessor in &block.declarations[1..] {
            let AssociatedDeclarationKind::Function(function) = &accessor.kind else {
                panic!("accessor")
            };
            assert!(function.block.is_some());
            assert!(matches!(
                function.signature.prototype.inputs[0].annotated_type.kind,
                TypeKind::ImplicitSelf
            ));
            assert!(function.signature.prototype.inputs[1].label.is_none());
        }
        let AssociatedDeclarationKind::Function(setter) = &block.declarations[2].kind else {
            unreachable!()
        };
        assert_ne!(
            setter.signature.prototype.inputs[1].name.symbol,
            setter.signature.prototype.inputs[2].name.symbol
        );
        let AssociatedDeclarationKind::Function(address) = &block.declarations[3].kind else {
            unreachable!()
        };
        assert!(matches!(
            address.signature.prototype.output.as_ref().unwrap().kind,
            TypeKind::Reference(_)
        ));
        #[derive(Default)]
        struct UniqueIds(std::collections::HashSet<NodeID>);
        impl ast::AstVisitor for UniqueIds {
            fn visit_type(&mut self, node: &Type) {
                assert!(self.0.insert(node.id), "reused type identity {:?}", node.id);
                ast::walk_type(self, node);
            }
            fn visit_function_parameter(&mut self, node: &FunctionParameter) {
                assert!(
                    self.0.insert(node.id),
                    "reused parameter identity {:?}",
                    node.id
                );
                ast::walk_function_parameter(self, node);
            }
            fn visit_expression(&mut self, node: &Expression) {
                assert!(
                    self.0.insert(node.id),
                    "reused expression identity {:?}",
                    node.id
                );
                ast::walk_expression(self, node);
            }
        }
        ast::walk_declaration(&mut UniqueIds::default(), &declaration);
    }

    #[test]
    fn native_subscript_explicit_accessors_replace_only_their_address_defaults() {
        let declaration = parse_one_decl(
            "extend Buffer { subscript(index: usize) -> Element { get { self.read(index) } address { self.at(index) } } }",
        );
        let DeclarationKind::Impl(block) = declaration.kind else {
            panic!("extend")
        };
        assert_eq!(block.declarations.len(), 4);
        let AssociatedDeclarationKind::Function(getter) = &block.declarations[1].kind else {
            panic!("getter")
        };
        assert!(
            matches!(getter.block.as_ref().unwrap().statements[0].kind, StatementKind::Expression(ref expression) if matches!(expression.kind, ExpressionKind::Call(..)))
        );
        let AssociatedDeclarationKind::Function(setter) = &block.declarations[2].kind else {
            panic!("setter")
        };
        assert!(
            matches!(setter.block.as_ref().unwrap().statements[0].kind, StatementKind::Expression(ref expression) if matches!(expression.kind, ExpressionKind::Assign(..)))
        );
    }

    #[test]
    fn native_subscript_index_parameters_initially_have_fixed_arity() {
        for inputs in ["", "index: usize = 0", "indices: usize...", "self", "&self"] {
            let source = format!(
                "extend Buffer {{ subscript({inputs}) -> Element {{ get {{ self.read() }} }} }}"
            );
            assert!(parse_decls(&source).is_err(), "accepted {source}");
        }
    }

    #[test]
    fn native_subscript_accessor_functions_reach_mir_without_index_protocols() {
        let errors = crate::test_support::analyze_script_mir_diagnostics(
            "struct Buffer { value: int32 }\nextend &Buffer { func at(_ index: usize) -> &int32 { &self.value }; subscript(index: usize) -> int32 { address { self.at(index) } } }\nfunc main() {}",
        );
        assert!(errors.is_empty(), "{errors:#?}");
    }

    #[test]
    fn computed_properties_use_implicit_getters_and_interface_defaults() {
        for source in [
            "extend Foo { var x: int32 { get { 1 } } }",
            "interface Foo { var x: int32 { get } }",
            "interface Foo { var x: int32 { get { 1 } } }",
        ] {
            let declarations = parse_decls(source).expect("implicit getter");
            let body = match &declarations[0].kind {
                DeclarationKind::Impl(block) => &block.declarations,
                DeclarationKind::Interface(interface) => &interface.declarations,
                _ => unreachable!(),
            };
            assert_eq!(body.len(), 2);
            let AssociatedDeclarationKind::Property(property) = &body[0].kind else {
                panic!("property")
            };
            assert_eq!(property.getter_id, body[1].id);
            let AssociatedDeclarationKind::Function(getter) = &body[1].kind else {
                panic!("getter")
            };
            assert!(matches!(
                getter.signature.prototype.inputs[0].annotated_type.kind,
                TypeKind::ImplicitSelf
            ));
            assert!(!getter.is_async);
        }
    }

    #[test]
    fn computed_properties_reject_removed_accessor_signatures_and_setters() {
        for accessor in [
            "get(self) { 1 }",
            "get(&self) { 1 }",
            "get async { 1 }",
            "get -> int32 { 1 }",
            "get { 1 } set(value) {}",
            "get { 1 } get { 2 }",
        ] {
            let source = format!("extend Foo {{ var x: int32 {{ {accessor} }} }}");
            assert!(parse_decls(&source).is_err(), "accepted {source}");
        }
    }

    #[test]
    fn g40_removed_computed_accessors_recover_without_cascading_declaration_errors() {
        for accessor in [
            "get(&self) { 1 }",
            "get async { 1 }",
            "get -> int32 { 1 }",
            "get { 1 } set(value) {}",
            "",
        ] {
            let source = format!(
                "extend Foo {{ var bad: int32 {{ {accessor} }}; var good: int32 {{ get {{ 2 }} }}; func ok() {{}}; }}\nfunc main() {{}}"
            );
            let (declarations, errors) = parse_decls_with_recovery(&source);
            assert_eq!(errors.len(), 1, "{accessor}: {errors:#?}");
            assert_eq!(declarations.len(), 2);
            let DeclarationKind::Impl(block) = &declarations[0].kind else {
                panic!("extension")
            };
            assert!(
                block
                    .declarations
                    .iter()
                    .any(|declaration| declaration.identifier.symbol.as_str() == "ok")
            );
        }
    }

    // ==================== ATTRIBUTE TESTS ====================

    #[test]
    fn test_simple_attribute() {
        let decl = parse_one_decl("@inline func foo() {}");
        assert_eq!(decl.attributes.len(), 1);
        assert_eq!(decl.attributes[0].identifier.symbol.as_str(), "inline");
        assert!(decl.attributes[0].args.is_none());
    }

    #[test]
    fn test_unsafe_attribute_removed() {
        let errors = parse_decls("@unsafe public func foo() {}").expect_err("parse should fail");
        assert_eq!(errors.len(), 1);
        assert!(matches!(
            errors[0].value,
            ParserError::UnsafeAttributeRemoved
        ));
    }

    #[test]
    fn deinit_reports_one_removed_syntax_error() {
        for source in [
            "extend Doc { deinit { value := 1 } }",
            "extend Doc { deinit {}; func keep() {}; }",
            "interface P { deinit {} }",
        ] {
            let errors = parse_decls(source).expect_err("deinit was removed");
            assert_eq!(errors.len(), 1, "{source}: {errors:?}");
            assert!(matches!(errors[0].value, ParserError::DeinitRemoved));
        }
    }

    #[test]
    fn test_attribute_with_key_value_string() {
        let decl = parse_one_decl(r#"@cfg(target_os = "macos") func foo() {}"#);
        assert_eq!(decl.attributes.len(), 1);
        assert_eq!(decl.attributes[0].identifier.symbol.as_str(), "cfg");
        let args = decl.attributes[0].args.as_ref().expect("Expected args");
        assert_eq!(args.items.len(), 1);
        match &args.items[0] {
            AttributeArg::KeyValue { key, value, .. } => {
                assert_eq!(key.symbol.as_str(), "target_os");
                match value {
                    Literal::String { value } => assert_eq!(value, "macos"),
                    _ => panic!("Expected string literal"),
                }
            }
            _ => panic!("Expected key-value arg"),
        }
    }

    #[test]
    fn test_attribute_with_multiple_args() {
        let decl =
            parse_one_decl(r#"@cfg(target_os = "linux", target_arch = "x86_64") func foo() {}"#);
        assert_eq!(decl.attributes.len(), 1);
        let args = decl.attributes[0].args.as_ref().expect("Expected args");
        assert_eq!(args.items.len(), 2);

        match &args.items[0] {
            AttributeArg::KeyValue { key, .. } => {
                assert_eq!(key.symbol.as_str(), "target_os")
            }
            _ => panic!("Expected key-value"),
        }
        match &args.items[1] {
            AttributeArg::KeyValue { key, .. } => {
                assert_eq!(key.symbol.as_str(), "target_arch")
            }
            _ => panic!("Expected key-value"),
        }
    }

    #[test]
    fn test_attribute_with_flag() {
        let decl = parse_one_decl("@cfg(test) func foo() {}");
        assert_eq!(decl.attributes.len(), 1);
        assert!(decl.attributes[0].args.is_none());
        match decl.attributes[0]
            .cfg_expr
            .as_ref()
            .expect("Expected cfg expression")
        {
            CfgExpr::Flag { name, .. } => {
                assert_eq!(name.symbol.as_str(), "test")
            }
            _ => panic!("Expected cfg flag expression"),
        }
    }

    #[test]
    fn test_multiple_attributes() {
        let decl = parse_one_decl(r#"@inline @cfg(target_os = "macos") func foo() {}"#);
        assert_eq!(decl.attributes.len(), 2);
        assert_eq!(decl.attributes[0].identifier.symbol.as_str(), "inline");
        assert_eq!(decl.attributes[1].identifier.symbol.as_str(), "cfg");
    }

    #[test]
    fn test_attribute_with_integer_value() {
        let decl = parse_one_decl("@version(major = 1) func foo() {}");
        assert_eq!(decl.attributes.len(), 1);
        let args = decl.attributes[0].args.as_ref().expect("Expected args");
        assert_eq!(args.items.len(), 1);
        match &args.items[0] {
            AttributeArg::KeyValue { key, value, .. } => {
                assert_eq!(key.symbol.as_str(), "major");
                assert!(matches!(value, Literal::Integer { .. }));
            }
            _ => panic!("Expected key-value"),
        }
    }

    #[test]
    fn test_attribute_with_integer_suffix_value() {
        let decl = parse_one_decl("@version(major = 1_i64) func foo() {}");
        assert_eq!(decl.attributes.len(), 1);
        let args = decl.attributes[0].args.as_ref().expect("Expected args");
        assert_eq!(args.items.len(), 1);
        match &args.items[0] {
            AttributeArg::KeyValue { key, value, .. } => {
                assert_eq!(key.symbol.as_str(), "major");
                assert!(matches!(
                    value,
                    Literal::Integer {
                        suffix: Some(IntegerTypeSuffix::I64),
                        ..
                    }
                ));
            }
            _ => panic!("Expected key-value"),
        }
    }

    #[test]
    fn test_attribute_with_positional_literal_arg() {
        let decl = parse_one_decl(r#"@doc("hello") func foo() {}"#);
        assert_eq!(decl.attributes.len(), 1);
        assert_eq!(decl.attributes[0].identifier.symbol.as_str(), "doc");

        let args = decl.attributes[0].args.as_ref().expect("Expected args");
        assert_eq!(args.items.len(), 1);

        match &args.items[0] {
            AttributeArg::Literal { value, .. } => match value {
                Literal::String { value } => assert_eq!(value, "hello"),
                _ => panic!("Expected string literal"),
            },
            _ => panic!("Expected literal"),
        }
    }

    #[test]
    fn test_tag_attribute_with_string_literals() {
        let decl = parse_one_decl(r#"@tag("smoke", "slow") func foo() {}"#);
        assert_eq!(decl.attributes.len(), 1);
        assert_eq!(decl.attributes[0].identifier.symbol.as_str(), "tag");

        let args = decl.attributes[0].args.as_ref().expect("Expected args");
        assert_eq!(args.items.len(), 2);
        match &args.items[0] {
            AttributeArg::Literal { value, .. } => match value {
                Literal::String { value } => assert_eq!(value, "smoke"),
                _ => panic!("Expected string literal"),
            },
            _ => panic!("Expected literal"),
        }
        match &args.items[1] {
            AttributeArg::Literal { value, .. } => match value {
                Literal::String { value } => assert_eq!(value, "slow"),
                _ => panic!("Expected string literal"),
            },
            _ => panic!("Expected literal"),
        }
    }

    fn parse_decls_with_recovery(input: &str) -> (Vec<Declaration>, Vec<Spanned<ParserError>>) {
        let mut parser = parser(input);
        let (decls, _module_decls) = parser
            .parse_module_declarations()
            .expect("recoverable declarations");
        (decls, parser.errors)
    }

    #[test]
    fn test_parser_recovery_declarations() {
        let input = "
            func good1() {}
            bad1 := 1;
            func good2() {}
            struct Bad2 { var }
            func good3() {}
        ";
        let (decls, errors) = parse_decls_with_recovery(input);
        assert!(!errors.is_empty(), "Should have parse errors");

        let func_count = decls
            .iter()
            .filter(|d| matches!(d.kind, DeclarationKind::Function(_)))
            .count();
        assert!(func_count >= 3, "Failed to recover all valid functions");
    }

    #[test]
    fn test_parser_recovery_statements() {
        let input = "func test() {
            x := 1;
            y := if if if;
            z := 2;
        }";
        let (decls, errors) = parse_decls_with_recovery(input);
        assert!(!errors.is_empty(), "Should have parse errors");

        let func = decls
            .into_iter()
            .find(|d| matches!(d.kind, DeclarationKind::Function(_)))
            .unwrap();
        if let DeclarationKind::Function(f) = func.kind {
            let body = f.block.unwrap();
            let let_count = body
                .statements
                .iter()
                .filter(|s| matches!(s.kind, StatementKind::Variable(_)))
                .count();
            assert!(let_count >= 2, "Failed to recover statements inside block");
        } else {
            panic!("Expected function");
        }
    }

    // ==================== ASYNC/AWAIT/SPAWN TESTS ====================

    #[test]
    fn test_async_function() {
        let decl = parse_one_decl("func fetch() async -> int32 {}");
        match &decl.kind {
            DeclarationKind::Function(func) => {
                assert!(func.is_async);
                assert!(!func.is_unsafe);
                assert!(func.signature.prototype.output.is_some());
                assert_eq!(decl.identifier.symbol.as_str(), "fetch");
            }
            _ => panic!("Expected function"),
        }
    }

    #[test]
    fn test_non_async_function_is_not_async() {
        let decl = parse_one_decl("func foo() -> int32 {}");
        match &decl.kind {
            DeclarationKind::Function(func) => {
                assert!(!func.is_async);
            }
            _ => panic!("Expected function"),
        }
    }

    #[test]
    fn test_async_function_no_return_type() {
        let decl = parse_one_decl("func fire() async {}");
        match &decl.kind {
            DeclarationKind::Function(func) => {
                assert!(func.is_async);
                assert!(func.signature.prototype.output.is_none());
            }
            _ => panic!("Expected function"),
        }
    }

    #[test]
    fn test_async_function_with_params() {
        let decl = parse_one_decl("func fetch(id: int64) async -> string {}");
        match &decl.kind {
            DeclarationKind::Function(func) => {
                assert!(func.is_async);
                assert_eq!(func.signature.prototype.inputs.len(), 1);
                assert!(func.signature.prototype.output.is_some());
            }
            _ => panic!("Expected function"),
        }
    }

    #[test]
    fn test_unsafe_async_function() {
        let decl = parse_one_decl("unsafe func fetch() async -> int32 {}");
        match &decl.kind {
            DeclarationKind::Function(func) => {
                assert!(func.is_unsafe);
                assert!(func.is_async);
            }
            _ => panic!("Expected function"),
        }
    }

    #[test]
    fn test_await_expression() {
        let expr = parse_expr_str("await foo()");
        match &expr.kind {
            ExpressionKind::Await(inner) => {
                assert!(matches!(inner.kind, ExpressionKind::Call(_, _)));
            }
            _ => panic!("Expected Await expression, got {:?}", expr.kind),
        }
    }

    #[test]
    fn test_await_simple_identifier() {
        let expr = parse_expr_str("await task");
        assert!(matches!(expr.kind, ExpressionKind::Await(_)));
    }

    #[test]
    fn test_spawn_is_identifier_expression() {
        let expr = parse_expr_str("spawn");
        assert!(matches!(expr.kind, ExpressionKind::Identifier(_)));
    }

    #[test]
    fn test_await_in_function_body() {
        let decl = parse_one_decl("func foo() async { x := await bar() }");
        match &decl.kind {
            DeclarationKind::Function(func) => {
                assert!(func.is_async);
                assert!(func.block.is_some());
            }
            _ => panic!("Expected function"),
        }
    }

    #[test]
    fn test_spawn_call_in_function_body() {
        let decl = parse_one_decl(
            "func foo() async { t := std::task::spawn(() async => { await bar() }) }",
        );
        match &decl.kind {
            DeclarationKind::Function(func) => {
                assert!(func.is_async);
                assert!(func.block.is_some());
            }
            _ => panic!("Expected function"),
        }
    }

    #[test]
    fn test_await_spawn_call() {
        let expr = parse_expr_str("await std::task::spawn(() async => { await foo() })");
        match &expr.kind {
            ExpressionKind::Await(inner) => {
                assert!(matches!(inner.kind, ExpressionKind::Call(_, _)));
            }
            _ => panic!("Expected Await(Call(...))"),
        }
    }
    #[test]
    fn named_field_constructors_and_patterns_parse() {
        let expression = parse_expr_str(".rect { width, height: 4 }");
        assert!(matches!(
            expression.kind,
            ExpressionKind::StructLiteral(StructLiteral {
                path: ConstructorPath::Inferred { .. },
                ..
            })
        ));
        let pattern = parse_pattern_str("Point[int32] { y: other, x, .. }");
        let PatternKind::PathNamed { fields, rest, .. } = pattern.kind else {
            panic!("named pattern")
        };
        assert!(rest);
        assert_eq!(fields.len(), 2);
        assert!(matches!(fields[1].pattern.kind, PatternKind::Identifier(_)));
    }

    #[test]
    fn named_field_duplicates_and_invalid_rest_are_diagnosed() {
        for (source, expected) in [
            (
                "func main() { var p = P { x: 1, x: 2 } }",
                "duplicate named field",
            ),
            (
                "func main() { match p { case P { x, x } => {} } }",
                "duplicate named field",
            ),
            (
                "func main() { match p { case P { .., x } => {} } }",
                "at the end of a named pattern",
            ),
            (
                "func main() { var p = P { x + 1 } }",
                "field shorthand requires",
            ),
        ] {
            let errors = parse_decls(source).expect_err("invalid named fields");
            assert!(
                errors
                    .iter()
                    .any(|error| error.value.to_string().contains(expected)),
                "{source}: {errors:?}"
            );
        }
    }
    #[test]
    fn struct_update_base_parses_after_fields() {
        for source in [
            "Pair { first: 3, ..base }",
            "Pair { first, ..make(), }",
            "Pair { ..base }",
        ] {
            let expression = parse_expr_str(source);
            let ExpressionKind::StructLiteral(literal) = expression.kind else {
                panic!("literal")
            };
            assert!(literal.base.is_some());
        }
    }
    #[test]
    fn struct_update_base_must_be_unique_and_final() {
        for source in [
            "func main() { var x = Pair { ..base, first: 1 } }",
            "func main() { var x = Pair { ..base, ..other } }",
        ] {
            let errors = parse_decls(source).expect_err("invalid update order");
            assert!(
                errors
                    .iter()
                    .any(|e| matches!(e.value, ParserError::StructUpdateBaseMustBeLast)),
                "{errors:?}"
            );
        }
    }
}

#[cfg(test)]
mod diagnostic_text_tests {
    use super::*;
    #[test]
    fn expected_tokens_use_source_spelling() {
        assert_eq!(
            ParserError::Expected(Token::RBrace, Token::Identifier { value: "b".into() })
                .to_string(),
            "expected `}`, found `b`"
        );
    }
    #[test]
    fn removed_const_reference_names_current_reference_form() {
        assert_eq!(
            ParserError::ReferenceConstModifier.to_string(),
            "`&const T` is removed; write `&T`"
        );
    }
}
