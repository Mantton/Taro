use crate::{ide::CompletionInfo, span::Position};

pub const COMPLETION_PROBE_IDENTIFIER: &str = "__taro_completion_probe";

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompletionContext {
    Lexical { prefix: String },
    Member { receiver: String, prefix: String },
    StaticMember { base: String, prefix: String },
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompletionProbeOverlay {
    pub source_text: String,
    pub position: Position,
    pub prefix: String,
    pub context: CompletionContext,
}

pub fn completion_context_at(source_text: &str, position: Position) -> CompletionContext {
    let Some(cursor_byte) = byte_index_for_position(source_text, position) else {
        return CompletionContext::Unknown;
    };
    let line_start = source_text[..cursor_byte]
        .rfind('\n')
        .map(|index| index + 1)
        .unwrap_or(0);
    let line_prefix = &source_text[line_start..cursor_byte];
    let prefix_start = identifier_prefix_start(line_prefix);
    let prefix = line_prefix[prefix_start..].to_string();
    let before_prefix = &line_prefix[..prefix_start];

    if let Some(before_dot) = before_prefix.strip_suffix('.') {
        if let Some(receiver) = dotted_receiver_before_dot(before_dot) {
            if is_static_receiver(&receiver) {
                return CompletionContext::StaticMember {
                    base: receiver,
                    prefix,
                };
            }
            return CompletionContext::Member { receiver, prefix };
        }
        return CompletionContext::Unknown;
    }

    CompletionContext::Lexical { prefix }
}

pub fn build_completion_probe_overlay(
    source_text: &str,
    position: Position,
    context: &CompletionContext,
) -> Option<CompletionProbeOverlay> {
    match context {
        CompletionContext::Member { prefix, .. }
        | CompletionContext::StaticMember { prefix, .. } => {
            let cursor_byte = byte_index_for_position(source_text, position)?;
            let prefix_byte_len = prefix.len();
            if cursor_byte < prefix_byte_len {
                return None;
            }
            let replacement_start = cursor_byte - prefix_byte_len;
            if !source_text.is_char_boundary(replacement_start) {
                return None;
            }

            let mut rewritten = String::with_capacity(
                source_text.len()
                    + COMPLETION_PROBE_IDENTIFIER
                        .len()
                        .saturating_sub(prefix.len()),
            );
            rewritten.push_str(&source_text[..replacement_start]);
            rewritten.push_str(COMPLETION_PROBE_IDENTIFIER);
            rewritten.push_str(&source_text[cursor_byte..]);

            let replacement_start_position = position_after_byte(source_text, replacement_start)?;
            let probe_position = Position {
                line: replacement_start_position.line,
                offset: replacement_start_position.offset
                    + COMPLETION_PROBE_IDENTIFIER.chars().count(),
            };

            Some(CompletionProbeOverlay {
                source_text: rewritten,
                position: probe_position,
                prefix: prefix.clone(),
                context: context.clone(),
            })
        }
        CompletionContext::Lexical { .. } | CompletionContext::Unknown => None,
    }
}

pub fn filter_completion_items_by_prefix(
    items: Vec<CompletionInfo>,
    prefix: &str,
) -> Vec<CompletionInfo> {
    if prefix.is_empty() {
        return items;
    }
    items
        .into_iter()
        .filter(|item| item.label.starts_with(prefix))
        .collect()
}

fn byte_index_for_position(source_text: &str, position: Position) -> Option<usize> {
    let mut current_line = 0usize;
    let mut line_start = 0usize;

    for (byte_index, ch) in source_text.char_indices() {
        if current_line == position.line {
            let mut line_byte = byte_index;
            for _ in 0..position.offset {
                if line_byte >= source_text.len() {
                    return None;
                }
                let next = source_text[line_byte..].chars().next()?;
                if next == '\n' {
                    return None;
                }
                line_byte += next.len_utf8();
            }
            return Some(line_byte);
        }

        if ch == '\n' {
            current_line += 1;
            line_start = byte_index + ch.len_utf8();
        }
    }

    if current_line == position.line {
        let mut line_byte = line_start;
        for _ in 0..position.offset {
            if line_byte >= source_text.len() {
                return None;
            }
            let next = source_text[line_byte..].chars().next()?;
            if next == '\n' {
                return None;
            }
            line_byte += next.len_utf8();
        }
        Some(line_byte)
    } else {
        None
    }
}

fn position_after_byte(source_text: &str, byte_index: usize) -> Option<Position> {
    if byte_index > source_text.len() || !source_text.is_char_boundary(byte_index) {
        return None;
    }

    let prefix = &source_text[..byte_index];
    let line = prefix.bytes().filter(|byte| *byte == b'\n').count();
    let line_start = prefix.rfind('\n').map(|index| index + 1).unwrap_or(0);
    let offset = source_text[line_start..byte_index].chars().count();
    Some(Position { line, offset })
}

fn identifier_prefix_start(line_prefix: &str) -> usize {
    let mut start = line_prefix.len();
    for (index, ch) in line_prefix.char_indices().rev() {
        if is_identifier_continue(ch) {
            start = index;
        } else {
            break;
        }
    }
    start
}

fn dotted_receiver_before_dot(before_dot: &str) -> Option<String> {
    let trimmed_end = before_dot.trim_end();
    if trimmed_end.len() != before_dot.len() {
        return None;
    }

    let mut start = trimmed_end.len();
    for (index, ch) in trimmed_end.char_indices().rev() {
        if is_identifier_continue(ch) || ch == '.' {
            start = index;
        } else {
            break;
        }
    }

    let receiver = &trimmed_end[start..];
    if receiver.is_empty()
        || receiver.starts_with('.')
        || receiver.ends_with('.')
        || receiver.split('.').any(|segment| !is_identifier(segment))
    {
        None
    } else {
        Some(receiver.to_string())
    }
}

fn is_static_receiver(receiver: &str) -> bool {
    receiver
        .rsplit('.')
        .next()
        .and_then(|segment| segment.chars().next())
        .map(|ch| ch.is_uppercase())
        .unwrap_or(false)
}

fn is_identifier(value: &str) -> bool {
    let mut chars = value.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    (first == '_' || first.is_alphabetic()) && chars.all(is_identifier_continue)
}

fn is_identifier_continue(ch: char) -> bool {
    ch == '_' || ch.is_alphanumeric()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn position_after(source: &str, needle: &str) -> Position {
        let byte_index = source.find(needle).expect("needle") + needle.len();
        position_after_byte(source, byte_index).expect("position")
    }

    #[test]
    fn context_detects_member_receiver_without_prefix() {
        let source = "func main() {\n    foo.\n}\n";
        assert_eq!(
            completion_context_at(source, position_after(source, "foo.")),
            CompletionContext::Member {
                receiver: "foo".into(),
                prefix: String::new()
            }
        );
    }

    #[test]
    fn context_detects_member_receiver_with_prefix() {
        let source = "func main() {\n    foo.b\n}\n";
        assert_eq!(
            completion_context_at(source, position_after(source, "foo.b")),
            CompletionContext::Member {
                receiver: "foo".into(),
                prefix: "b".into()
            }
        );
    }

    #[test]
    fn context_detects_static_receiver_with_prefix() {
        let source = "func main() {\n    pkg.Heading.n\n}\n";
        assert_eq!(
            completion_context_at(source, position_after(source, "pkg.Heading.n")),
            CompletionContext::StaticMember {
                base: "pkg.Heading".into(),
                prefix: "n".into()
            }
        );
    }

    #[test]
    fn context_detects_static_receiver_without_prefix() {
        let source = "func main() {\n    Heading.\n}\n";
        assert_eq!(
            completion_context_at(source, position_after(source, "Heading.")),
            CompletionContext::StaticMember {
                base: "Heading".into(),
                prefix: String::new()
            }
        );
    }

    #[test]
    fn context_detects_lexical_prefix() {
        let source = "func main() {\n    loc\n}\n";
        assert_eq!(
            completion_context_at(source, position_after(source, "loc")),
            CompletionContext::Lexical {
                prefix: "loc".into()
            }
        );
    }

    #[test]
    fn probe_overlay_replaces_member_prefix() {
        let source = "func main() {\n    foo.b\n}\n";
        let position = position_after(source, "foo.b");
        let context = completion_context_at(source, position);
        let overlay = build_completion_probe_overlay(source, position, &context).expect("overlay");

        assert!(overlay.source_text.contains("foo.__taro_completion_probe"));
        assert_eq!(overlay.prefix, "b");
        assert_eq!(
            overlay.position,
            position_after(&overlay.source_text, "__taro_completion_probe")
        );
    }

    #[test]
    fn probe_overlay_handles_unicode_before_cursor() {
        let source = "func main() {\n    let 😀 = 1\n    foo.b\n}\n";
        let position = position_after(source, "foo.b");
        let context = completion_context_at(source, position);
        let overlay = build_completion_probe_overlay(source, position, &context).expect("overlay");

        assert_eq!(overlay.prefix, "b");
        assert_eq!(
            overlay.position,
            position_after(&overlay.source_text, "__taro_completion_probe")
        );
    }
}
