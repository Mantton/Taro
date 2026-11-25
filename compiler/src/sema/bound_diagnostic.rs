//! Declaration-checked messages for failed interface requirements. Attributes
//! already travel in package metadata, so source and imported bounds share
//! the same renderer.
use crate::{
    compile::context::Gcx,
    hir::{Attribute, AttributeArg, DefinitionID, KnownAttribute, Literal},
    sema::models::Ty,
    span::{Span, Symbol},
};

fn literal(attribute: &Attribute) -> Option<(Symbol, Span)> {
    match attribute.args.as_ref()?.items.as_slice() {
        [
            AttributeArg::Literal {
                value: Literal::String(text),
                span,
            },
        ] => Some((*text, *span)),
        _ => None,
    }
}

/// Only {Self} is substituted. Consume escaped braces in this pass so
/// inserted type names and escaped placeholder spellings are never rescanned.
fn render(mut template: &str, self_name: &str) -> Result<String, &'static str> {
    if template.trim().is_empty() {
        return Err("@onUnsatisfied requires a nonempty message");
    }
    let mut result = String::with_capacity(template.len());
    while let Some(index) = template.find(['{', '}']) {
        result.push_str(&template[..index]);
        let rest = &template[index..];
        if let Some(tail) = rest.strip_prefix("{Self}") {
            result.push_str(self_name);
            template = tail;
        } else if let Some(tail) = rest.strip_prefix("{{") {
            result.push('{');
            template = tail;
        } else if let Some(tail) = rest.strip_prefix("}}") {
            result.push('}');
            template = tail;
        } else {
            return Err(
                "invalid @onUnsatisfied template: use {Self} for the type and {{ or }} for literal braces",
            );
        }
    }
    result.push_str(template);
    Ok(result)
}

pub(crate) fn validate(gcx: Gcx<'_>, attributes: &[Attribute], is_interface: bool) {
    let mut seen = false;
    for attribute in attributes
        .iter()
        .filter(|attr| attr.as_known(gcx) == Some(KnownAttribute::OnUnsatisfied))
    {
        let issue = if !is_interface {
            Some((
                "@onUnsatisfied is only allowed on interfaces",
                attribute.span,
            ))
        } else if seen {
            Some(("duplicate @onUnsatisfied on interface", attribute.span))
        } else if let Some((text, span)) = literal(attribute) {
            render(text.as_str(), "{Self}")
                .err()
                .map(|error| (error, span))
        } else {
            Some((
                "@onUnsatisfied requires exactly one string literal",
                attribute.span,
            ))
        };
        if let Some((error, span)) = issue {
            gcx.dcx().emit_error(error.into(), Some(span));
        }
        seen = true;
    }
}

pub(crate) fn message<'ctx>(
    gcx: Gcx<'ctx>,
    interface: DefinitionID,
    ty: Ty<'ctx>,
) -> Option<String> {
    let attr = gcx
        .attributes_of(interface)
        .iter()
        .find(|attr| attr.as_known(gcx) == Some(KnownAttribute::OnUnsatisfied))?;
    let (text, _) = literal(attr)?;
    render(text.as_str(), &ty.format(gcx)).ok()
}
