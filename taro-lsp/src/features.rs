//! Convert current compiler facts into editor responses.

use std::{collections::BTreeMap, path::Path, sync::Arc};

use compiler::{
    compile::{
        analysis_products::{
            AnalysisDiagnostic, AnalysisProduct, Argument, ConstantArgument, ConstantArgumentValue,
            OwnedConstant, SourceRange, TypeShape, TypedOccurrence,
        },
        source::{SourceText, Utf16Position},
    },
    diagnostics::DiagnosticLevel,
    span::Position,
};
use lsp_types::{
    CompletionItem, CompletionItemKind, Diagnostic, DiagnosticRelatedInformation,
    DiagnosticSeverity, Hover, HoverContents, Location, MarkupContent, MarkupKind, NumberOrString,
    Range, Uri,
};

use crate::supervisor::Supervisor;

pub fn hover(workspace: &Supervisor, path: &Path, position: lsp_types::Position) -> Option<Hover> {
    let occurrence = occurrence(workspace, path, position)?;
    let description = describe(&occurrence.ty)?;
    Some(Hover {
        contents: HoverContents::Markup(MarkupContent {
            kind: MarkupKind::PlainText,
            value: description,
        }),
        range: readable_range(workspace, &occurrence.source),
    })
}

pub fn definition(
    workspace: &Supervisor,
    path: &Path,
    position: lsp_types::Position,
) -> Option<Location> {
    let occurrence = occurrence(workspace, path, position)?;
    let destination = occurrence
        .local_declaration
        .as_ref()
        .map(|binding| &binding.source)
        .or_else(|| {
            occurrence
                .declaration
                .as_ref()
                .map(|declaration| &declaration.source)
        })?;
    location(workspace, destination)
}

pub fn completions(
    workspace: &Supervisor,
    path: &Path,
    position: lsp_types::Position,
) -> Option<Vec<CompletionItem>> {
    let product = workspace.current()?;
    let position = scalar_position(workspace, path, position)?;
    let site = product
        .missing_members
        .iter()
        .find(|site| site.insertion.path == path && site.insertion.start == position)?;
    Some(
        site.items
            .iter()
            .map(|item| CompletionItem {
                label: item.name.clone(),
                kind: Some(if item.is_method {
                    CompletionItemKind::METHOD
                } else {
                    CompletionItemKind::FIELD
                }),
                detail: item.detail.clone(),
                ..CompletionItem::default()
            })
            .collect(),
    )
}

pub fn diagnostics(
    workspace: &Supervisor,
    analysis: &AnalysisProduct,
) -> BTreeMap<Uri, Vec<Diagnostic>> {
    let mut files = BTreeMap::<Uri, Vec<Diagnostic>>::new();
    for source in &analysis.diagnostics {
        let Some((uri, diagnostic)) = diagnostic(workspace, source) else {
            continue;
        };
        files.entry(uri).or_default().push(diagnostic);
    }
    files
}

fn diagnostic(workspace: &Supervisor, source: &AnalysisDiagnostic) -> Option<(Uri, Diagnostic)> {
    let site = source
        .source
        .as_ref()
        .and_then(|source| location(workspace, source))?;
    let related_information = source
        .notes
        .iter()
        .filter_map(|note| {
            Some(DiagnosticRelatedInformation {
                location: location(workspace, note.source.as_ref()?)?,
                message: note.message.clone(),
            })
        })
        .collect::<Vec<_>>();
    let code = source
        .code
        .and_then(|code| i32::try_from(code).ok())
        .map(NumberOrString::Number);
    Some((
        site.uri,
        Diagnostic {
            range: site.range,
            severity: Some(match source.level {
                DiagnosticLevel::Error => DiagnosticSeverity::ERROR,
                DiagnosticLevel::Warn => DiagnosticSeverity::WARNING,
                DiagnosticLevel::Info => DiagnosticSeverity::INFORMATION,
            }),
            code,
            source: Some("taro".into()),
            message: source.message.clone(),
            related_information: (!related_information.is_empty()).then_some(related_information),
            ..Diagnostic::default()
        },
    ))
}

fn occurrence<'a>(
    workspace: &'a Supervisor,
    path: &Path,
    position: lsp_types::Position,
) -> Option<&'a TypedOccurrence> {
    let position = scalar_position(workspace, path, position)?;
    workspace
        .current()?
        .occurrences
        .iter()
        .filter(|fact| {
            fact.source.path == path && fact.source.start <= position && position < fact.source.end
        })
        .min_by_key(|fact| {
            let source = &fact.source;
            let lines = source.end.line - source.start.line;
            let columns = if lines == 0 {
                source.end.offset - source.start.offset
            } else {
                source.end.offset
            };
            (
                lines,
                columns,
                fact.declaration.is_none() && fact.local_declaration.is_none(),
            )
        })
}

fn scalar_position(
    workspace: &Supervisor,
    path: &Path,
    position: lsp_types::Position,
) -> Option<Position> {
    workspace.source_text(path)?.from_utf16(Utf16Position {
        line: position.line,
        column: position.character,
    })
}

fn readable_range(workspace: &Supervisor, source: &SourceRange) -> Option<Range> {
    let text: Arc<SourceText> = workspace.source_text(&source.path)?;
    let to_lsp = |position| {
        let utf16 = text.to_utf16(position)?;
        Some(lsp_types::Position::new(utf16.line, utf16.column))
    };
    Some(Range::new(to_lsp(source.start)?, to_lsp(source.end)?))
}

fn location(workspace: &Supervisor, source: &SourceRange) -> Option<Location> {
    Some(Location::new(
        workspace.document_uri(&source.path)?,
        readable_range(workspace, source)?,
    ))
}

fn describe(ty: &TypeShape) -> Option<String> {
    fn many(types: &[TypeShape]) -> Option<String> {
        Some(
            types
                .iter()
                .map(describe)
                .collect::<Option<Vec<_>>>()?
                .join(", "),
        )
    }
    let description = match ty {
        TypeShape::Bool => "bool".into(),
        TypeShape::Rune => "rune".into(),
        TypeShape::String => "string".into(),
        TypeShape::Int(number) => number.name_str().into(),
        TypeShape::UInt(number) => number.name_str().into(),
        TypeShape::Float(number) => number.name_str().into(),
        TypeShape::Array { element, len } => format!("[{}; {}]", describe(element)?, constant(len)),
        TypeShape::Nominal {
            declaration,
            arguments,
            ..
        }
        | TypeShape::Alias {
            declaration,
            arguments,
            ..
        } => {
            let name = &declaration.as_ref()?.name;
            if arguments.is_empty() {
                name.clone()
            } else {
                let arguments = arguments
                    .iter()
                    .map(|argument| match argument {
                        Argument::Type(ty) => describe(ty),
                        Argument::Constant(value) => Some(constant(value)),
                    })
                    .collect::<Option<Vec<_>>>()?;
                format!("{name}[{}]", arguments.join(", "))
            }
        }
        TypeShape::Pointer(ty, mutability) => {
            let flavor = if mutability.display_str().is_empty() {
                "*const "
            } else {
                "*"
            };
            format!("{flavor}{}", describe(ty)?)
        }
        TypeShape::Reference(ty) => format!("&{}", describe(ty)?),
        TypeShape::Tuple(elements) => format!(
            "({})",
            elements
                .iter()
                .map(|element| {
                    let ty = describe(&element.ty)?;
                    Some(
                        element
                            .label
                            .as_ref()
                            .map_or_else(|| ty.clone(), |label| format!("{label}: {ty}")),
                    )
                })
                .collect::<Option<Vec<_>>>()?
                .join(", ")
        ),
        TypeShape::Function { inputs, output, .. } | TypeShape::Closure { inputs, output, .. } => {
            format!("({}) -> {}", many(inputs)?, describe(output)?)
        }
        TypeShape::Parameter { name, .. } => name.clone(),
        TypeShape::Never => "!".into(),
        TypeShape::Error
        | TypeShape::Unresolved
        | TypeShape::ExistentialSelf(_)
        | TypeShape::Interfaces(_)
        | TypeShape::Opaque(_) => return None,
    };
    Some(description)
}

fn constant(argument: &ConstantArgument) -> String {
    match &argument.value {
        ConstantArgumentValue::Literal(OwnedConstant::Integer(value)) => value.to_string(),
        ConstantArgumentValue::Literal(OwnedConstant::Bool(value)) => value.to_string(),
        ConstantArgumentValue::Parameter { name, .. } => name.clone(),
        _ => "_".into(),
    }
}
