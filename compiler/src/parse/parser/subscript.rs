//! Native subscript accessors use ordinary implicit method receivers. Keeping
//! their identities in the declaration preserves capabilities through lowering.
use super::*;

impl Parser {
    pub(super) fn parse_native_subscript(
        &mut self,
        start: Span,
        attributes: AttributeList,
        visibility: Visibility,
        body_required: bool,
        is_final: bool,
        is_override: bool,
    ) -> R<Vec<AssociatedDeclaration>> {
        let identifier = self.parse_identifier()?;
        let header_start = self.cursor;
        let inputs = self.parse_function_parameters()?;
        if inputs.is_empty()
            || inputs.iter().any(|p| {
                p.is_variadic || p.default_value.is_some() || self.symbol_eq(p.name.symbol, "self")
            })
        {
            return Err(Spanned::new(
                ParserError::InvalidSubscriptSignature,
                identifier.span,
            ));
        }
        self.expect(Token::RArrow)?;
        let ty = self.parse_type()?;
        // Replay only this short signature for each accessor. Each function
        // needs fresh syntax identities, including paths and const expressions;
        // shallow-cloning parameters would alias resolver/type-checker entries.
        let mut header = self.file.tokens[header_start..self.cursor].to_vec();
        header.push(Spanned::new(Token::EOF, ty.span));
        self.expect(Token::LBrace)?;
        let mut getter = None;
        let mut setter = None;
        let mut address = None;
        while !self.matches(Token::RBrace) && !self.is_at_end() {
            while self.eat(Token::Semicolon) {}
            if self.matches(Token::RBrace) {
                break;
            }
            let accessor = self.parse_identifier()?;
            let slot = match accessor.symbol.as_str() {
                "get" => &mut getter,
                "set" => &mut setter,
                "address" => &mut address,
                _ => {
                    return Err(Spanned::new(
                        ParserError::InvalidSubscriptAccessor,
                        accessor.span,
                    ));
                }
            };
            if slot.is_some() {
                return Err(Spanned::new(
                    ParserError::DuplicateSubscriptAccessor,
                    accessor.span,
                ));
            }
            let value = if self.symbol_eq(accessor.symbol, "set") {
                if self.eat(Token::LParen) {
                    let value = self.parse_identifier()?;
                    self.expect(Token::RParen)?;
                    if self.symbol_eq(value.symbol, "self")
                        || inputs.iter().any(|p| p.name.symbol == value.symbol)
                    {
                        return Err(Spanned::new(
                            ParserError::InvalidSubscriptAccessor,
                            value.span,
                        ));
                    }
                    Some(value)
                } else if body_required || self.matches(Token::LBrace) {
                    return Err(Spanned::new(
                        ParserError::InvalidSubscriptAccessor,
                        accessor.span,
                    ));
                } else {
                    None
                }
            } else {
                None
            };
            let block = if self.matches(Token::LBrace) {
                Some(self.parse_block()?)
            } else if body_required {
                return Err(self.err_at_current(ParserError::FunctionBodyRequired));
            } else {
                None
            };
            *slot = Some(self.native_accessor(
                &header,
                accessor,
                value,
                block,
                visibility,
                is_final,
                is_override,
            )?);
        }
        self.expect(Token::RBrace)?;
        self.eat(Token::Semicolon);
        if getter.is_none() && address.is_none() && !(is_override && setter.is_some()) {
            return Err(Spanned::new(
                ParserError::MissingSubscriptRead,
                identifier.span,
            ));
        }
        let getter_is_default = getter.is_none() && address.is_some();
        let setter_is_default = setter.is_none() && address.is_some();
        if address.is_some() {
            for (kind, slot) in [("get", &mut getter), ("set", &mut setter)] {
                if slot.is_none() {
                    let accessor = Identifier {
                        symbol: self.intern_symbol(kind),
                        span: identifier.span,
                    };
                    let mut declaration = self.native_accessor(
                        &header,
                        accessor,
                        None,
                        None,
                        visibility,
                        is_final,
                        is_override,
                    )?;
                    let AssociatedDeclarationKind::Function(function) = &mut declaration.kind
                    else {
                        unreachable!()
                    };
                    function.block =
                        Some(self.native_address_default(&function.signature, kind == "set"));
                    *slot = Some(declaration);
                }
            }
        }
        // Accessors are the callable definitions used by MIR and codegen. Keep
        // the subscript's inline policy on explicit and address-default bodies.
        // Other declaration attributes (for example tests) are not accessor policy.
        let inline_policy: AttributeList = attributes
            .iter()
            .filter(|attribute| {
                matches!(attribute.identifier.symbol.as_str(), "inline" | "noinline")
            })
            .cloned()
            .collect();
        for accessor in [&mut getter, &mut setter, &mut address]
            .into_iter()
            .flatten()
        {
            accessor.attributes.extend(inline_policy.iter().cloned());
        }
        let declaration = Declaration {
            id: self.next_id(),
            span: start.to(self.hi_span()),
            identifier,
            visibility,
            attributes,
            kind: AssociatedDeclarationKind::Subscript(ast::NativeSubscript {
                ty,
                getter_id: getter.as_ref().map(|d| d.id),
                setter_id: setter.as_ref().map(|d| d.id),
                address_id: address.as_ref().map(|d| d.id),
                getter_is_default,
                setter_is_default,
                is_override,
                is_final,
            }),
        };
        let mut declarations = vec![declaration];
        declarations.extend(getter);
        declarations.extend(setter);
        declarations.extend(address);
        Ok(declarations)
    }

    fn native_accessor(
        &mut self,
        header: &[Spanned<Token>],
        accessor: Identifier,
        value: Option<Identifier>,
        block: Option<Block>,
        visibility: Visibility,
        is_final: bool,
        is_override: bool,
    ) -> R<AssociatedDeclaration> {
        let mut parser = Parser::new(
            lexer::File {
                id: self.file.id,
                tokens: header.to_vec(),
            },
            self.next_index.clone(),
        );
        let mut inputs = parser.parse_function_parameters()?;
        parser.expect(Token::RArrow)?;
        let output = parser.parse_type()?;
        self.errors.extend(parser.errors);
        self.warnings.extend(parser.warnings);
        for input in &mut inputs {
            // A bare name is an unlabeled index; explicit external labels are
            // preserved, as on ordinary methods.
            if input
                .label
                .as_ref()
                .is_some_and(|l| l.identifier.symbol == input.name.symbol)
            {
                input.label = None;
            }
        }
        inputs.insert(
            0,
            FunctionParameter {
                id: self.next_id(),
                attributes: vec![],
                label: None,
                name: Identifier {
                    symbol: self.intern_symbol("self"),
                    span: accessor.span,
                },
                annotated_type: Box::new(Type {
                    id: self.next_id(),
                    span: accessor.span,
                    kind: TypeKind::ImplicitSelf,
                }),
                default_value: None,
                is_variadic: false,
                span: accessor.span,
            },
        );
        let output = match accessor.symbol.as_str() {
            "set" => {
                let value = value.unwrap_or_else(|| {
                    let mut name = "__subscript_value".to_owned();
                    while inputs
                        .iter()
                        .any(|input| self.symbol_eq(input.name.symbol, &name))
                    {
                        name.push('_');
                    }
                    Identifier {
                        symbol: self.intern_symbol(&name),
                        span: accessor.span,
                    }
                });
                inputs.push(FunctionParameter {
                    id: self.next_id(),
                    attributes: vec![],
                    label: None,
                    name: value,
                    annotated_type: output,
                    default_value: None,
                    is_variadic: false,
                    span: accessor.span,
                });
                None
            }
            "address" => Some(Box::new(Type {
                id: self.next_id(),
                span: output.span,
                kind: TypeKind::Reference(output),
            })),
            _ => Some(output),
        };
        Ok(Declaration {
            id: self.next_id(),
            span: accessor.span,
            visibility,
            attributes: vec![],
            identifier: Identifier {
                symbol: self.intern_symbol(&format!("__subscript_{}", accessor.symbol.as_str())),
                span: accessor.span,
            },
            kind: AssociatedDeclarationKind::Function(Function {
                generics: Generics {
                    type_parameters: None,
                    where_clause: None,
                },
                signature: FunctionSignature {
                    span: accessor.span,
                    prototype: FunctionPrototype { inputs, output },
                },
                block,
                is_unsafe: false,
                is_async: false,
                is_final,
                is_override,
                abi: None,
            }),
        })
    }

    fn native_address_default(&mut self, signature: &FunctionSignature, setter: bool) -> Block {
        let span = signature.span;
        let receiver = self.native_identifier(signature.prototype.inputs[0].name);
        let callee = Box::new(Expression {
            id: self.next_id(),
            span,
            kind: ExpressionKind::Member {
                target: receiver,
                name: Identifier {
                    symbol: self.intern_symbol("__subscript_address"),
                    span,
                },
                qualified: false,
            },
        });
        let end = signature.prototype.inputs.len() - usize::from(setter);
        let args = signature.prototype.inputs[1..end]
            .iter()
            .map(|input| ExpressionArgument {
                label: input.label.clone(),
                span: input.span,
                expression: self.native_identifier(input.name),
            })
            .collect();
        let call = Box::new(Expression {
            id: self.next_id(),
            span,
            kind: ExpressionKind::Call(callee, args),
        });
        let place = Box::new(Expression {
            id: self.next_id(),
            span,
            kind: ExpressionKind::Dereference(call),
        });
        let expression = if setter {
            let value = self.native_identifier(signature.prototype.inputs.last().unwrap().name);
            Box::new(Expression {
                id: self.next_id(),
                span,
                kind: ExpressionKind::Assign(place, value),
            })
        } else {
            place
        };
        Block {
            id: self.next_id(),
            span,
            has_declarations: false,
            statements: vec![Statement {
                id: self.next_id(),
                span,
                kind: StatementKind::Expression(expression),
            }],
        }
    }

    fn native_identifier(&mut self, name: Identifier) -> Box<Expression> {
        Box::new(Expression {
            id: self.next_id(),
            span: name.span,
            kind: ExpressionKind::Identifier(name),
        })
    }
}
