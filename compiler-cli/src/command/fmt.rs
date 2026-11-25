use std::{
    fs,
    path::{Path, PathBuf},
};

use compiler::{constants::FILE_EXTENSION, error::ReportedError};

use crate::{
    FmtArgs,
    command::{CommandOutcome, CommandResult},
};

const INDENT: &str = "    ";

pub fn run(arguments: FmtArgs) -> CommandResult {
    let mut files = Vec::new();
    for path in &arguments.paths {
        collect_taro_files(path, &mut files).map_err(|err| {
            eprintln!("error: {err}");
            ReportedError
        })?;
    }
    files.sort();
    files.dedup();

    if files.is_empty() {
        if !arguments.check {
            println!("No .{FILE_EXTENSION} files found.");
        }
        return Ok(CommandOutcome::Success);
    }

    let mut drifted = Vec::new();
    let mut formatted_count = 0usize;
    let mut had_error = false;

    for path in &files {
        let original = match fs::read_to_string(path) {
            Ok(content) => content,
            Err(err) => {
                eprintln!("error: failed to read '{}': {err}", path.display());
                had_error = true;
                continue;
            }
        };

        let formatted = match format_source(&original) {
            Ok(formatted) => formatted,
            Err(err) => {
                eprintln!("error: failed to format '{}': {err}", path.display());
                had_error = true;
                continue;
            }
        };

        if formatted != original {
            if arguments.check {
                println!("Diff in {}", path.display());
                drifted.push(path.clone());
            } else {
                if let Err(err) = fs::write(path, &formatted) {
                    eprintln!("error: failed to write '{}': {err}", path.display());
                    had_error = true;
                    continue;
                }
                formatted_count += 1;
            }
        }
    }

    if had_error {
        return Err(ReportedError);
    }

    if arguments.check {
        if !drifted.is_empty() {
            eprintln!(
                "error: {} file{} would be reformatted",
                drifted.len(),
                if drifted.len() == 1 { "" } else { "s" }
            );
            return Ok(CommandOutcome::ChildExit(1));
        }
        return Ok(CommandOutcome::Success);
    }

    if formatted_count > 0 {
        println!(
            "Formatted {} file{}.",
            formatted_count,
            if formatted_count == 1 { "" } else { "s" }
        );
    }

    Ok(CommandOutcome::Success)
}

fn collect_taro_files(path: &Path, out: &mut Vec<PathBuf>) -> Result<(), String> {
    let meta = fs::metadata(path)
        .map_err(|err| format!("failed to access '{}': {err}", path.display()))?;
    if meta.is_file() {
        if path.extension().and_then(|e| e.to_str()) == Some(FILE_EXTENSION) {
            out.push(path.to_path_buf());
        } else {
            return Err(format!(
                "expected a .{FILE_EXTENSION} file or directory, got '{}'",
                path.display()
            ));
        }
        return Ok(());
    }

    if meta.is_dir() {
        let mut entries: Vec<PathBuf> = fs::read_dir(path)
            .map_err(|err| format!("failed to read directory '{}': {err}", path.display()))?
            .filter_map(|e| e.ok().map(|e| e.path()))
            .collect();
        entries.sort();
        for entry in entries {
            let Some(name) = entry.file_name().and_then(|n| n.to_str()) else {
                continue;
            };
            if name.starts_with('.') || name == "target" || name == "dist" || name == "node_modules"
            {
                continue;
            }
            if entry.is_dir() {
                collect_taro_files(&entry, out)?;
            } else if entry.extension().and_then(|e| e.to_str()) == Some(FILE_EXTENSION) {
                out.push(entry);
            }
        }
    }
    Ok(())
}

/// Format one Taro source file using the standard library's canonical style
/// while preserving comments, raw/multiline string boundaries, nested
/// interpolation, and ASI line-break semantics.
pub fn format_source(source: &str) -> Result<String, String> {
    let normalized = source.replace("\r\n", "\n").replace('\r', "\n");
    let items = scan_lossless(&normalized)?;
    let formatted = render_items(&items);

    // Self-check: ensure the original and formatted source both lex cleanly
    // and produce the exact same semantic token stream (including ASI-inserted
    // semicolons, literals, and nested interpolations).
    compiler::verify_format_equivalence(source, &formatted)?;

    Ok(formatted)
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ItemKind {
    Newline,
    LineComment,
    BlockComment,
    /// Single- or multi-line string / raw string / byte string / rune literal.
    Literal,
    IdentOrKeyword,
    Number,
    Punct,
}

#[derive(Debug, Clone)]
struct Item {
    start: usize,
    kind: ItemKind,
    text: String,
}

/// Losslessly scan Taro source into code tokens, verbatim literals (including
/// raw literals, multiline strings, and nested interpolations), comments, and
/// newlines. Horizontal whitespace outside literals/comments is discarded so it
/// can be emitted canonically.
fn scan_lossless(src: &str) -> Result<Vec<Item>, String> {
    let bytes = src.as_bytes();
    let len = bytes.len();
    let mut i = 0usize;
    let mut items = Vec::new();

    while i < len {
        let start_offset = i;
        let b = bytes[i];
        if b == b' ' || b == b'\t' {
            i += 1;
            continue;
        }
        if b == b'\n' {
            items.push(Item {
                start: start_offset,
                kind: ItemKind::Newline,
                text: "\n".to_string(),
            });
            i += 1;
            continue;
        }

        // Line comment (`//...` or `///...`)
        if b == b'/' && i + 1 < len && bytes[i + 1] == b'/' {
            let start = i;
            i += 2;
            while i < len && bytes[i] != b'\n' {
                i += 1;
            }
            let text = src[start..i].trim_end_matches([' ', '\t']).to_string();
            items.push(Item {
                start: start_offset,
                kind: ItemKind::LineComment,
                text,
            });
            continue;
        }

        // Nested block comment (`/* ... */`)
        if b == b'/' && i + 1 < len && bytes[i + 1] == b'*' {
            let start = i;
            i = scan_block_comment(bytes, i)?;
            let text = src[start..i].to_string();
            items.push(Item {
                start: start_offset,
                kind: ItemKind::BlockComment,
                text,
            });
            continue;
        }

        // Taro raw strings: `#"..."#`, `##"..."##`, `#"""..."""#`, with `$#{...}` interpolation.
        if let Some(end) = try_scan_raw_string(bytes, i)? {
            let text = src[i..end].to_string();
            items.push(Item {
                start: start_offset,
                kind: ItemKind::Literal,
                text,
            });
            i = end;
            continue;
        }

        // Byte string `b"..."` / `b"""..."""`
        if b == b'b' && i + 1 < len && bytes[i + 1] == b'"' {
            let start = i;
            i = scan_quoted_string(bytes, i + 1, false)?;
            let text = src[start..i].to_string();
            items.push(Item {
                start: start_offset,
                kind: ItemKind::Literal,
                text,
            });
            continue;
        }

        // Regular or multiline string `"..."` / `"""..."""` (with nested `${...}`)
        if b == b'"' {
            let start = i;
            i = scan_quoted_string(bytes, i, true)?;
            let text = src[start..i].to_string();
            items.push(Item {
                start: start_offset,
                kind: ItemKind::Literal,
                text,
            });
            continue;
        }

        if b == b'`' {
            i = scan_escaped_identifier(bytes, i)?;
            items.push(Item {
                start: start_offset,
                kind: ItemKind::IdentOrKeyword,
                text: src[start_offset..i].to_string(),
            });
            continue;
        }

        // Rune literal `'...'`
        if b == b'\'' {
            let start = i;
            i += 1;
            while i < len {
                if bytes[i] == b'\\' && i + 1 < len {
                    i += 2;
                    continue;
                }
                if bytes[i] == b'\'' {
                    i += 1;
                    break;
                }
                i += 1;
            }
            items.push(Item {
                start: start_offset,
                kind: ItemKind::Literal,
                text: src[start..i].to_string(),
            });
            continue;
        }

        // Numeric literal (including hex/bin/oct, underscores, float exponents, suffixes)
        if b.is_ascii_digit() {
            let start = i;
            i = scan_number(bytes, i);
            items.push(Item {
                start: start_offset,
                kind: ItemKind::Number,
                text: src[start..i].to_string(),
            });
            continue;
        }

        // Identifier or keyword (UTF-8 aware)
        let ch = src[i..].chars().next().unwrap();
        if ch == '_' || ch.is_alphabetic() {
            let start = i;
            i += ch.len_utf8();
            while i < len {
                let c = src[i..].chars().next().unwrap();
                if c == '_' || c.is_alphanumeric() {
                    i += c.len_utf8();
                } else {
                    break;
                }
            }
            items.push(Item {
                start: start_offset,
                kind: ItemKind::IdentOrKeyword,
                text: src[start..i].to_string(),
            });
            continue;
        }

        // Multi-character operators & punctuation (longest match first)
        let punct = match_punct(&src[i..]);
        let plen = punct.len();
        items.push(Item {
            start: start_offset,
            kind: ItemKind::Punct,
            text: punct.to_string(),
        });
        i += plen;
    }

    Ok(items)
}

fn scan_escaped_identifier(bytes: &[u8], start: usize) -> Result<usize, String> {
    let mut i = start + 1;
    while let Some(&b) = bytes.get(i) {
        match b {
            b'`' => return Ok(i + 1),
            b'\n' => break,
            b'\\' if matches!(bytes.get(i + 1), Some(b'`' | b'\\')) => i += 2,
            _ => i += 1,
        }
    }
    Err("unterminated escaped identifier".to_string())
}

fn scan_block_comment(bytes: &[u8], start: usize) -> Result<usize, String> {
    let len = bytes.len();
    let mut i = start + 2;
    let mut depth = 1usize;
    while i < len && depth > 0 {
        if bytes[i] == b'/' && i + 1 < len && bytes[i + 1] == b'*' {
            depth += 1;
            i += 2;
        } else if bytes[i] == b'*' && i + 1 < len && bytes[i + 1] == b'/' {
            depth -= 1;
            i += 2;
        } else {
            i += 1;
        }
    }
    if depth != 0 {
        return Err("unterminated block comment".to_string());
    }
    Ok(i)
}

fn try_scan_raw_string(bytes: &[u8], start: usize) -> Result<Option<usize>, String> {
    let len = bytes.len();
    if bytes[start] != b'#' {
        return Ok(None);
    }

    let mut i = start;
    while i < len && bytes[i] == b'#' {
        i += 1;
    }
    let hashes = i - start;
    if i >= len || bytes[i] != b'"' {
        return Ok(None);
    }

    let is_triple = i + 2 < len && bytes[i + 1] == b'"' && bytes[i + 2] == b'"';
    let delim_quotes = if is_triple { 3 } else { 1 };
    i += delim_quotes;

    while i < len {
        // Raw string interpolation: `$` + `hashes` `#`s + `{ ... }`
        if bytes[i] == b'$' && i + 1 + hashes < len {
            let mut h = 0;
            while h < hashes && bytes[i + 1 + h] == b'#' {
                h += 1;
            }
            if h == hashes && bytes[i + 1 + hashes] == b'{' {
                i = scan_interpolation_hole(bytes, i + 2 + hashes)?;
                continue;
            }
        }
        if bytes[i] == b'"' {
            let mut q = 0;
            while i + q < len && bytes[i + q] == b'"' && q < delim_quotes {
                q += 1;
            }
            if q == delim_quotes {
                let mut h = 0;
                while i + delim_quotes + h < len
                    && bytes[i + delim_quotes + h] == b'#'
                    && h < hashes
                {
                    h += 1;
                }
                if h == hashes {
                    return Ok(Some(i + delim_quotes + hashes));
                }
            }
        }
        i += 1;
    }
    Err("unterminated raw string literal".to_string())
}

fn scan_quoted_string(bytes: &[u8], start: usize, allow_interp: bool) -> Result<usize, String> {
    let len = bytes.len();
    let is_triple = start + 2 < len && bytes[start + 1] == b'"' && bytes[start + 2] == b'"';
    let mut i = start + if is_triple { 3 } else { 1 };

    while i < len {
        if bytes[i] == b'\\' && i + 1 < len {
            i += 2;
            continue;
        }
        if allow_interp && bytes[i] == b'$' && i + 1 < len && bytes[i + 1] == b'{' {
            i = scan_interpolation_hole(bytes, i + 2)?;
            continue;
        }
        if is_triple {
            if bytes[i] == b'"' && i + 2 < len && bytes[i + 1] == b'"' && bytes[i + 2] == b'"' {
                return Ok(i + 3);
            }
        } else if bytes[i] == b'"' {
            return Ok(i + 1);
        }
        i += 1;
    }
    Err("unterminated string literal".to_string())
}

fn scan_interpolation_hole(bytes: &[u8], start: usize) -> Result<usize, String> {
    let len = bytes.len();
    let mut i = start;
    let mut depth = 1usize;
    while i < len && depth > 0 {
        let b = bytes[i];
        if b == b'`' {
            i = scan_escaped_identifier(bytes, i)?;
            continue;
        }
        if b == b'/' && i + 1 < len && bytes[i + 1] == b'/' {
            i += 2;
            while i < len && bytes[i] != b'\n' {
                i += 1;
            }
            continue;
        }
        if b == b'/' && i + 1 < len && bytes[i + 1] == b'*' {
            i = scan_block_comment(bytes, i)?;
            continue;
        }
        if let Some(end) = try_scan_raw_string(bytes, i)? {
            i = end;
            continue;
        }
        if b == b'b' && i + 1 < len && bytes[i + 1] == b'"' {
            i = scan_quoted_string(bytes, i + 1, false)?;
            continue;
        }
        if b == b'"' {
            i = scan_quoted_string(bytes, i, true)?;
            continue;
        }
        if b == b'\'' {
            i += 1;
            while i < len {
                if bytes[i] == b'\\' && i + 1 < len {
                    i += 2;
                    continue;
                }
                if bytes[i] == b'\'' {
                    i += 1;
                    break;
                }
                i += 1;
            }
            continue;
        }
        if b == b'{' {
            depth += 1;
            i += 1;
        } else if b == b'}' {
            depth -= 1;
            i += 1;
        } else {
            i += 1;
        }
    }
    if depth != 0 {
        return Err("unterminated string interpolation".to_string());
    }
    Ok(i)
}

fn scan_number(bytes: &[u8], start: usize) -> usize {
    let len = bytes.len();
    let mut i = start;
    if bytes[i] == b'0'
        && i + 1 < len
        && matches!(bytes[i + 1], b'x' | b'X' | b'b' | b'B' | b'o' | b'O')
    {
        i += 2;
        while i < len && (bytes[i].is_ascii_hexdigit() || bytes[i] == b'_') {
            i += 1;
        }
    } else {
        while i < len && (bytes[i].is_ascii_digit() || bytes[i] == b'_') {
            i += 1;
        }
        // Decimal fraction only if followed by a digit (so `0..10` and `1.toString()` stay separate).
        if i + 1 < len && bytes[i] == b'.' && bytes[i + 1].is_ascii_digit() {
            i += 1;
            while i < len && (bytes[i].is_ascii_digit() || bytes[i] == b'_') {
                i += 1;
            }
        }
        // Exponent `e+10` / `E-5`
        if i < len && matches!(bytes[i], b'e' | b'E') {
            let exp_start = i;
            i += 1;
            if i < len && matches!(bytes[i], b'+' | b'-') {
                i += 1;
            }
            if i < len && bytes[i].is_ascii_digit() {
                while i < len && (bytes[i].is_ascii_digit() || bytes[i] == b'_') {
                    i += 1;
                }
            } else {
                i = exp_start;
            }
        }
    }
    // Optional type suffix like `_i64`, `_u8`, `_f64`, `i32`, `u64`
    if i < len && (bytes[i].is_ascii_alphabetic() || bytes[i] == b'_') {
        while i < len && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
            i += 1;
        }
    }
    i
}

fn match_punct(s: &str) -> &str {
    if let Some(rest) = s.strip_prefix("!in") {
        let next_is_ident = rest
            .chars()
            .next()
            .is_some_and(|c| c == '_' || c.is_alphanumeric());
        if !next_is_ident {
            return "!in";
        }
    }
    if s.starts_with("?...") {
        return "?";
    }
    const MULTI: &[&str] = &[
        "===", "!==", "..=", "...", "<<=", ">>=", "??=", ":=", "->", "=>", "::", "..", "??", "?.",
        ".*", "|>", "==", "!=", "<=", ">=", "&&", "||", "+=", "-=", "*=", "/=", "%=", "&=", "|=",
        "^=", "<<", ">>",
    ];
    for op in MULTI {
        if s.starts_with(op) {
            return op;
        }
    }
    let ch = s.chars().next().unwrap();
    &s[..ch.len_utf8()]
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DelimKind {
    Brace { is_import: bool },
    Paren,
    Bracket,
}

#[derive(Debug, Clone, Copy)]
struct OpenDelim {
    kind: DelimKind,
    line: usize,
}

fn render_items(items: &[Item]) -> String {
    // Group items into physical source lines (keeping multiline literals/comments
    // attached to the line on which they begin).
    let mut lines: Vec<Vec<&Item>> = vec![Vec::new()];
    for item in items {
        if item.kind == ItemKind::Newline {
            lines.push(Vec::new());
        } else {
            lines.last_mut().unwrap().push(item);
        }
    }

    // Trim leading & trailing empty lines.
    while lines.first().is_some_and(|l| l.is_empty()) {
        lines.remove(0);
    }
    while lines.last().is_some_and(|l| l.is_empty()) {
        lines.pop();
    }

    if lines.is_empty() {
        return String::new();
    }

    let mut out = String::new();
    let mut stack: Vec<OpenDelim> = Vec::new();
    let mut blank_run = 0usize;
    let mut prev_ended_with_open_brace = false;
    let mut prev_code_token: Option<&Item> = None;

    for (line_idx, line) in lines.iter().enumerate() {
        if line.is_empty() {
            // Suppress blank lines right after `{` or right before a closing `}`,
            // and collapse multiple consecutive blank lines to at most one.
            let next_starts_with_close_brace = lines[line_idx + 1..]
                .iter()
                .find(|l| !l.is_empty())
                .and_then(|l| l.first())
                .is_some_and(|it| it.kind == ItemKind::Punct && it.text == "}");
            if !prev_ended_with_open_brace && !next_starts_with_close_brace && blank_run == 0 {
                out.push('\n');
                blank_run += 1;
            }
            continue;
        }

        blank_run = 0;

        // Pop any leading closing delimiters before computing this line's indent.
        let mut leading_closes = 0usize;
        for item in line {
            if item.kind == ItemKind::Punct && matches!(item.text.as_str(), "}" | ")" | "]") {
                leading_closes += 1;
            } else {
                break;
            }
        }
        let mut temp_stack = stack.clone();
        for item in line.iter().take(leading_closes) {
            pop_matching(&mut temp_stack, &item.text);
        }

        let mut indent_level = compute_indent_level(&temp_stack);
        // Dot-continued method chains (e.g. `.map(...)`) indent one extra level
        // when not already inside a continuation group.
        let starts_with_dot = line
            .first()
            .is_some_and(|it| it.kind == ItemKind::Punct && it.text == ".");
        let in_group = temp_stack
            .iter()
            .any(|d| matches!(d.kind, DelimKind::Paren | DelimKind::Bracket));
        let prev_continues_member = prev_code_token.is_some_and(|t| {
            !(t.kind == ItemKind::Punct && matches!(t.text.as_str(), "{" | ";" | "," | ":" | "=>"))
        });
        if starts_with_dot && !in_group && prev_continues_member {
            indent_level += 1;
        }

        for _ in 0..indent_level {
            out.push_str(INDENT);
        }

        // Render tokens on this line with canonical std-style spacing while
        // updating the real delimiter stack.
        let line_is_type_header = line.first().is_some_and(|it| {
            it.kind == ItemKind::IdentOrKeyword && matches!(it.text.as_str(), "extend" | "conform")
        });
        let mut prev_on_line: Option<&Item> = None;
        let mut prev_prev_on_line: Option<&Item> = None;
        for (idx, item) in line.iter().enumerate() {
            let next_on_line = line.get(idx + 1).copied();
            if let Some(prev) = prev_on_line {
                if needs_space(
                    prev_prev_on_line,
                    prev,
                    item,
                    next_on_line,
                    &stack,
                    line_is_type_header,
                ) {
                    out.push(' ');
                }
            }
            out.push_str(&item.text);

            // Update delimiter stack on code punctuation.
            if item.kind == ItemKind::Punct {
                match item.text.as_str() {
                    "{" => {
                        let is_import = prev_on_line
                            .is_some_and(|p| p.kind == ItemKind::Punct && p.text == "::");
                        stack.push(OpenDelim {
                            kind: DelimKind::Brace { is_import },
                            line: line_idx,
                        });
                    }
                    "(" => {
                        stack.push(OpenDelim {
                            kind: DelimKind::Paren,
                            line: line_idx,
                        });
                    }
                    "[" => {
                        stack.push(OpenDelim {
                            kind: DelimKind::Bracket,
                            line: line_idx,
                        });
                    }
                    "}" | ")" | "]" => {
                        pop_matching(&mut stack, &item.text);
                    }
                    _ => {}
                }
            }

            if !matches!(item.kind, ItemKind::LineComment | ItemKind::BlockComment) {
                prev_code_token = Some(item);
            }
            prev_prev_on_line = prev_on_line;
            prev_on_line = Some(item);
        }

        out.push('\n');
        prev_ended_with_open_brace = prev_code_token
            .is_some_and(|t| t.kind == ItemKind::Punct && t.text == "{")
            && line
                .iter()
                .rev()
                .find(|t| !matches!(t.kind, ItemKind::LineComment | ItemKind::BlockComment))
                .is_some_and(|t| t.kind == ItemKind::Punct && t.text == "{");
    }

    out
}

fn pop_matching(stack: &mut Vec<OpenDelim>, close: &str) {
    let matches_top = |d: OpenDelim| match close {
        "}" => matches!(d.kind, DelimKind::Brace { .. }),
        ")" => matches!(d.kind, DelimKind::Paren),
        "]" => matches!(d.kind, DelimKind::Bracket),
        _ => false,
    };
    if let Some(pos) = stack.iter().rposition(|&d| matches_top(d)) {
        stack.truncate(pos);
    }
}

fn compute_indent_level(stack: &[OpenDelim]) -> usize {
    let mut level = 0usize;
    let mut seen_group_lines = Vec::new();
    for entry in stack {
        match entry.kind {
            DelimKind::Brace { .. } => level += 1,
            DelimKind::Paren | DelimKind::Bracket => {
                if !seen_group_lines.contains(&entry.line) {
                    seen_group_lines.push(entry.line);
                    level += 1;
                }
            }
        }
    }
    level
}

fn is_keyword_not_operand(text: &str) -> bool {
    matches!(
        text,
        "func"
            | "struct"
            | "enum"
            | "class"
            | "interface"
            | "extend"
            | "conform"
            | "type"
            | "namespace"
            | "import"
            | "export"
            | "extern"
            | "public"
            | "internal"
            | "private"
            | "static"
            | "async"
            | "await"
            | "unsafe"
            | "final"
            | "override"
            | "required"
            | "convenience"
            | "var"
            | "let"
            | "const"
            | "mut"
            | "if"
            | "else"
            | "while"
            | "for"
            | "in"
            | "loop"
            | "match"
            | "case"
            | "guard"
            | "return"
            | "break"
            | "continue"
            | "defer"
            | "where"
            | "as"
            | "is"
            | "to"
            | "from"
            | "try"
            | "move"
            | "any"
            | "some"
            | "init"
    )
}

fn ends_operand(item: &Item) -> bool {
    match item.kind {
        ItemKind::Number | ItemKind::Literal => true,
        ItemKind::IdentOrKeyword => !is_keyword_not_operand(&item.text),
        ItemKind::Punct => matches!(item.text.as_str(), ")" | "]" | "}" | "?" | "!"),
        ItemKind::Newline | ItemKind::LineComment | ItemKind::BlockComment => false,
    }
}

fn is_binary_only_op(op: &str) -> bool {
    matches!(
        op,
        "=" | ":="
            | "+="
            | "-="
            | "*="
            | "/="
            | "%="
            | "&="
            | "|="
            | "^="
            | "<<="
            | ">>="
            | "??="
            | "??"
            | "==="
            | "!=="
            | "=="
            | "!="
            | "!in"
            | "|>"
            | "<="
            | ">="
            | "<"
            | ">"
            | "&&"
            | "||"
            | "+"
            | "/"
            | "%"
            | "|"
            | "^"
            | "<<"
            | ">>"
            | "=>"
            | "->"
    )
}

fn is_prefix_unary(prev_prev: Option<&Item>, prev: &Item, line_is_type_header: bool) -> bool {
    if prev.kind != ItemKind::Punct {
        return false;
    }
    match prev.text.as_str() {
        "!" => prev_prev.map_or(true, |pp| !ends_operand(pp)),
        "~" => true,
        "&" | "*" if line_is_type_header => true,
        "-" | "&" | "*" => prev_prev.map_or(true, |pp| !ends_operand(pp)),
        _ => false,
    }
}

fn needs_space(
    prev_prev: Option<&Item>,
    prev: &Item,
    curr: &Item,
    _next: Option<&Item>,
    stack: &[OpenDelim],
    line_is_type_header: bool,
) -> bool {
    // Comments always get a separating space around them.
    if matches!(curr.kind, ItemKind::LineComment | ItemKind::BlockComment) {
        return true;
    }
    if matches!(prev.kind, ItemKind::BlockComment) {
        return !matches!(curr.kind, ItemKind::Punct if matches!(curr.text.as_str(), "," | ";" | ")" | "]" | "."));
    }

    let p = prev.text.as_str();
    let c = curr.text.as_str();

    // The parser uses these gaps to distinguish a yield expression from
    // calls, subscripts and binary operations on a variable named yield.
    if p == "yield" || (prev_prev.is_some_and(|item| item.text == "yield")
        && matches!(p, "-" | "*" | "&" | "&&")) {
        return curr.start > prev.start + prev.text.len();
    }

    // No space immediately after opening parens/brackets or `@`/`#`.
    if prev.kind == ItemKind::Punct && matches!(p, "(" | "[" | "@" | "#") {
        return false;
    }

    // No space before closing parens/brackets, comma, semicolon, colon.
    if curr.kind == ItemKind::Punct && matches!(c, ")" | "]" | "," | ";" | ":") {
        return false;
    }

    // `::` never has surrounding spaces.
    if (prev.kind == ItemKind::Punct && p == "::") || (curr.kind == ItemKind::Punct && c == "::") {
        return false;
    }

    // `..`, `..=`, `...` range & spread operators.
    if prev.kind == ItemKind::Punct && matches!(p, ".." | "..=" | "...") {
        if p == ".." {
            return (curr.kind == ItemKind::Punct && (c == "{" || is_binary_only_op(c)))
                || (curr.kind == ItemKind::IdentOrKeyword && is_keyword_not_operand(c));
        }
        return false;
    }
    if curr.kind == ItemKind::Punct && matches!(c, ".." | "..=" | "...") {
        if c == "..." {
            return false;
        }
        // `Foo { a: 1, ..base }`, `r := ..10`, `x in ..10` -> space before `..`/`..=`;
        // `0..10`, `xs[..3]`, `(..3)` -> no space before `..`/`..=`.
        return !ends_operand(prev) && !(prev.kind == ItemKind::Punct && matches!(p, "(" | "["));
    }

    // `.`, `?.`, `.*` member access / optional chaining / deref / leading enum shorthand.
    if prev.kind == ItemKind::Punct && matches!(p, "." | "?." | ".*") {
        return false;
    }
    if curr.kind == ItemKind::Punct && matches!(c, "?." | ".*") {
        return false;
    }
    if curr.kind == ItemKind::Punct && c == "." {
        // `foo.bar`, `a().b`, `arr[0].c` -> no space; `return .none`, `x == .none`, `case .a` -> space.
        return !ends_operand(prev) && !(prev.kind == ItemKind::Punct && matches!(p, "(" | "[" | "."));
    }

    // Braces `{` and `}`.
    let in_import_brace = matches!(
        stack.last().map(|d| d.kind),
        Some(DelimKind::Brace { is_import: true })
    );
    if curr.kind == ItemKind::Punct && c == "{" {
        if prev.kind == ItemKind::Punct && matches!(p, "(" | "[" | "{" | "::") {
            return false;
        }
        return true;
    }
    if prev.kind == ItemKind::Punct && p == "{" {
        if curr.kind == ItemKind::Punct && c == "}" {
            return false;
        }
        return !in_import_brace;
    }
    if curr.kind == ItemKind::Punct && c == "}" {
        return !in_import_brace;
    }

    // `(` and `[` openers.
    if curr.kind == ItemKind::Punct && c == "(" {
        if prev.kind == ItemKind::Punct {
            return is_binary_only_op(p)
                || matches!(p, "," | ";" | ":" | "{" | "}" | "-" | "&" | "*");
        }
        // `foo(x)`, `List[T](x)` -> no space; `if (x)`, `return (a, b)` -> space.
        return prev.kind == ItemKind::IdentOrKeyword && is_keyword_not_operand(p)
            && !prev_prev.is_some_and(|t| matches!(t.text.as_str(), "." | "?." | "::"));
    }
    if curr.kind == ItemKind::Punct && c == "[" {
        if prev.kind == ItemKind::Punct {
            return is_binary_only_op(p)
                || matches!(p, "," | ";" | ":" | "{" | "}" | "-" | "&" | "*");
        }
        // `func foo[T]`, `extend[T]`, `List[int64]`, `arr[0]` -> no space!
        if prev.kind == ItemKind::IdentOrKeyword
            && matches!(p, "extend" | "conform" | "struct" | "enum" | "class" | "interface")
        {
            return false;
        }
        return prev.kind == ItemKind::IdentOrKeyword && is_keyword_not_operand(p)
            && !prev_prev.is_some_and(|t| matches!(t.text.as_str(), "." | "?." | "::"));
    }

    // Comma, semicolon, colon always take a space after.
    if prev.kind == ItemKind::Punct && matches!(p, "," | ";" | ":") {
        return true;
    }

    // `?` (optional suffix `T?` or `as?`) and `!` (unary `!x` or postfix `try!`).
    if curr.kind == ItemKind::Punct && c == "?" {
        return false;
    }
    if prev.kind == ItemKind::Punct && p == "?" {
        return true;
    }
    if curr.kind == ItemKind::Punct && c == "!" {
        // Postfix `expr!` has no space; prefix `!cond` follows keyword/op spacing.
        return !ends_operand(prev);
    }
    if prev.kind == ItemKind::Punct && p == "!" {
        // Prefix `!cond` has no space after; postfix `expr! + 1` has space before next token.
        return !is_prefix_unary(prev_prev, prev, line_is_type_header);
    }

    // Unary prefix `-`, `&`, `*`, `~`: no space after!
    if is_prefix_unary(prev_prev, prev, line_is_type_header) {
        return false;
    }

    // Binary operators always take spaces on both sides.
    if (prev.kind == ItemKind::Punct && is_binary_only_op(p))
        || (curr.kind == ItemKind::Punct && is_binary_only_op(c))
    {
        return true;
    }
    if (prev.kind == ItemKind::Punct && matches!(p, "-" | "&" | "*"))
        || (curr.kind == ItemKind::Punct && matches!(c, "-" | "&" | "*"))
    {
        return true;
    }

    // Adjacent keywords/identifiers/literals/closing delimiters separated by one space.
    true
}

#[cfg(test)]
mod tests {
    use super::format_source;

    #[test]
    fn preserves_contextual_yield_and_escaped_identifiers() {
        let source = r#"func g(_ xs: int32?...) {
    yield -1
    yield *p
    yield (1 + 2)
    yield - 2
    yield(6)
    yield .some(1)
    `percent %s test`(`type`)
    println("${`}`}")
}
"#;
        assert_eq!(format_source(source).unwrap(), source);
    }

    #[test]
    fn formats_std_style_and_is_idempotent() {
        let messy = r#"import  std::ops::{ Fn , PartialEq }

public func   add[ T: PartialEq ]( _  a: int64 , _  b: int64 ) -> int64{
    if  a==b {
        return  a+b
    } else{
        return  a - b
    }
}
"#;
        let once = format_source(messy).expect("first format");
        let twice = format_source(&once).expect("second format");
        assert_eq!(once, twice, "formatter must be idempotent");
        assert_eq!(
            once,
            r#"import std::ops::{Fn, PartialEq}

public func add[T: PartialEq](_ a: int64, _ b: int64) -> int64 {
    if a == b {
        return a + b
    } else {
        return a - b
    }
}
"#
        );
    }

    #[test]
    fn preserves_comments_raw_strings_multiline_strings_and_nested_interpolation() {
        let src = r###"/// Doc comment stays intact
func demo(_ name: string) -> string {
    // Line comment
    raw := #"C:\notes\   "world"   ${not interp} $#{name}"#
    raw2 := ##"a "# b $##{name}"##
    nested := "outer ${"inner ${1 + 2}"} end" /* block /* nested */ comment */
    multi := #"""
        line one
        Hello, $#{name}
        """#
    return "${raw} ${raw2} ${nested} ${multi}"
}
"###;
        let once = format_source(src).expect("format with comments/literals");
        let twice = format_source(&once).expect("second format");
        assert_eq!(once, twice);
        assert!(once.contains("/// Doc comment stays intact"));
        assert!(once.contains("// Line comment"));
        assert!(once.contains(r##"#"C:\notes\   "world"   ${not interp} $#{name}"#"##));
        assert!(once.contains(r###"##"a "# b $##{name}"##"###));
        assert!(once.contains(r#""outer ${"inner ${1 + 2}"} end""#));
        assert!(once.contains("/* block /* nested */ comment */"));
        assert!(once.contains("        line one\n        Hello, $#{name}\n        \"\"\"#"));
    }

    #[test]
    fn preserves_asi_sensitive_newlines_and_pointer_unary_syntax() {
        let src = r#"extend[T] &Box[T] {
    public func demo(_ ptr: *const uint8, _ out: *mut uint8) -> int64 {
        x := -1
        y := x - 2
        xs := [
            1,
            2,
            3,
        ]
        val := foo(
            bar(1, 2),
        )
        if !flag {
            return y
        } else {
            return x
        }
    }
}
"#;
        let once = format_source(src).expect("format ASI-sensitive code");
        let twice = format_source(&once).expect("second format");
        assert_eq!(once, twice);
        assert!(once.contains("extend[T] &Box[T] {"));
        assert!(once.contains("*const uint8, _ out: *mut uint8"));
        assert!(once.contains("x := -1"));
        assert!(once.contains("y := x - 2"));
        assert!(once.contains("if !flag {"));
    }

    #[test]
    fn preserves_identity_membership_and_chaining_operators() {
        let src = "func check(_ a: int64, _ b: int64) -> bool {\n    return a !in 0..b && a === b && a !== b\n}\n";
        let once = format_source(src).expect("format operators");
        let twice = format_source(&once).expect("second format");
        assert_eq!(once, twice);
        assert!(once.contains("a !in 0..b && a === b && a !== b"));
    }
}
