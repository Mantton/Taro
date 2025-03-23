use super::package::{Parser, R};
use taroc_ast::{
    ConformanceConstraint, GenericBound, GenericBounds, GenericRequirement, GenericRequirementList,
    GenericWhereClause, Inheritance, RequiredTypeConstraint, TypeArguments, TypeParameter,
    TypeParameterKind, TypeParameters,
};
use taroc_span::SpannedMessage;
use taroc_token::{Delimiter, TokenKind};

impl Parser {
    pub fn parse_type_arguments(&mut self) -> R<TypeArguments> {
        let lo = self.lo_span();
        let tys =
            self.parse_delimiter_sequence(Delimiter::Chevron, TokenKind::Comma, false, |p| {
                p.parse_type()
            })?;

        let args = TypeArguments {
            span: lo.to(self.hi_span()),
            arguments: tys,
        };

        Ok(args)
    }
}

impl Parser {
    pub fn parse_type_parameters(&mut self) -> R<Option<TypeParameters>> {
        let lo = self.lo_span();
        if !self.matches(TokenKind::LChevron) {
            return Ok(None);
        }

        let parameters =
            self.parse_delimiter_sequence(Delimiter::Chevron, TokenKind::Comma, false, |p| {
                p.parse_type_parameter()
            })?;

        let t = TypeParameters {
            span: lo.to(self.hi_span()),
            parameters,
        };

        Ok(Some(t))
    }
    pub fn parse_type_parameter(&mut self) -> R<TypeParameter> {
        if self.matches(TokenKind::Const) {
            self.parse_const_type_parameter()
        } else {
            self.parse_normal_type_parameter()
        }
    }

    pub fn parse_const_type_parameter(&mut self) -> R<TypeParameter> {
        let lo = self.lo_span();
        self.expect(TokenKind::Const)?;
        let identifier = self.parse_identifier()?;
        self.expect(TokenKind::Colon)?;
        let ty = self.parse_type()?;

        let default = if self.eat(TokenKind::Assign) {
            Some(self.parse_anon_const()?)
        } else {
            None
        };

        let span = lo.to(self.hi_span());
        let kind = TypeParameterKind::Constant { ty, default };

        let tp = TypeParameter {
            identifier,
            span,
            bounds: None,
            kind,
        };

        Ok(tp)
    }
    pub fn parse_normal_type_parameter(&mut self) -> R<TypeParameter> {
        let lo = self.lo_span();

        let identifier = self.parse_identifier()?;

        let bounds = if self.eat(TokenKind::Colon) {
            Some(self.parse_generic_bounds()?)
        } else {
            None
        };

        let default = if self.eat(TokenKind::Assign) {
            Some(self.parse_type()?)
        } else {
            None
        };

        let kind = TypeParameterKind::Type { default };

        let span = lo.to(self.hi_span());

        let tp = TypeParameter {
            identifier,
            span,
            bounds,
            kind,
        };

        Ok(tp)
    }
}

impl Parser {
    pub fn parse_generic_bounds(&mut self) -> R<GenericBounds> {
        let bounds = self.parse_sequence(TokenKind::Amp, |p| p.parse_generic_bound())?;
        Ok(bounds)
    }

    pub fn parse_generic_bound(&mut self) -> R<GenericBound> {
        let path = self.parse_path()?;
        Ok(GenericBound { path })
    }
}

impl Parser {
    pub fn parse_generic_where_clause(&mut self) -> R<Option<GenericWhereClause>> {
        let lo = self.lo_span();
        if !self.eat(TokenKind::Where) {
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
        self.parse_sequence(TokenKind::Comma, |p| p.parse_generic_requirement())
    }

    fn parse_generic_requirement(&mut self) -> R<GenericRequirement> {
        let lo = self.lo_span();
        let bounded_type = self.parse_path()?;
        let kind = if self.eat(TokenKind::Eql) {
            let bound = self.parse_type()?;
            let kind = RequiredTypeConstraint {
                bounded_type,
                bound,
                span: lo.to(self.hi_span()),
            };
            GenericRequirement::SameTypeRequirement(kind)
        } else if self.eat(TokenKind::Colon) {
            let bounds = self.parse_generic_bounds()?;
            let kind = ConformanceConstraint {
                bounded_type,
                bounds,
                span: lo.to(self.hi_span()),
            };
            GenericRequirement::ConformanceRequirement(kind)
        } else {
            let msg = format!("expected generic requirement",);
            let err = SpannedMessage::new(msg, self.current_token_span());
            return Err(err);
        };

        return Ok(kind);
    }
}

impl Parser {
    pub fn can_parse_type_arguments(&mut self) -> bool {
        self.with_anchor(|p| {
            let v = p.parse_type_arguments();

            if v.is_err() {
                return false;
            }

            return TokenKind::is_generic_type_disambiguating_token(p.current_kind());
        })
    }
}

impl Parser {
    pub fn parse_inheritance(&mut self) -> R<Option<Inheritance>> {
        if self.eat(TokenKind::Colon) {
            let interfaces = self.parse_sequence(TokenKind::Comma, |this| this.parse_path())?;
            let node = Inheritance { interfaces };
            Ok(Some(node))
        } else {
            Ok(None)
        }
    }
}
