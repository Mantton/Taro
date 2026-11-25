use std::{
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
};

use compiler::{
    diagnostics::Suggestion,
    error::ReportedError,
    span::Span,
};

use crate::{
    FixArgs,
    command::{CommandOutcome, CommandResult, check},
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SourceEdit {
    pub start_byte: usize,
    pub end_byte: usize,
    pub line_1_based: usize,
    pub col_0_based: usize,
    pub replacement: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ApplyResult {
    pub updated: String,
    pub applied: usize,
    pub skipped_overlaps: Vec<SourceEdit>,
}

pub fn run(arguments: FixArgs) -> CommandResult {
    let dry_run = arguments.dry_run;
    let dcx = check::run_collecting_diagnostics(arguments.common)?;
    let suggestions = dcx.machine_applicable_suggestions();

    if suggestions.is_empty() {
        println!("No machine-applicable fixes to apply.");
        return Ok(CommandOutcome::Success);
    }

    let mut by_file: BTreeMap<PathBuf, Vec<Suggestion>> = BTreeMap::new();
    for suggestion in suggestions {
        let Some(path) = dcx.file_path(suggestion.span.file) else {
            eprintln!(
                "warning: skipping fix with unknown file id {}",
                suggestion.span.file.raw()
            );
            continue;
        };
        by_file.entry(path).or_default().push(suggestion);
    }

    let mut total_applied = 0usize;
    let mut total_files = 0usize;
    let mut total_overlaps = 0usize;

    for (path, file_suggestions) in by_file {
        let content = fs::read_to_string(&path).map_err(|err| {
            eprintln!("error: failed to read '{}': {err}", path.display());
            ReportedError
        })?;

        let mut edits = Vec::new();
        for suggestion in file_suggestions {
            match span_to_byte_range(&content, suggestion.span) {
                Some((start_byte, end_byte)) => edits.push(SourceEdit {
                    start_byte,
                    end_byte,
                    line_1_based: suggestion.span.start.line + 1,
                    col_0_based: suggestion.span.start.offset,
                    replacement: suggestion.replacement,
                }),
                None => {
                    eprintln!(
                        "warning: skipping fix with out-of-range span in '{}:{}:{}'",
                        path.display(),
                        suggestion.span.start.line + 1,
                        suggestion.span.start.offset
                    );
                }
            }
        }

        let result = apply_edits_to_source(&content, &edits);
        for skipped in &result.skipped_overlaps {
            total_overlaps += 1;
            eprintln!(
                "warning: skipping overlapping fix at {}:{}:{} (replacement '{}')",
                path.display(),
                skipped.line_1_based,
                skipped.col_0_based,
                skipped.replacement
            );
        }

        if result.applied == 0 || result.updated == content {
            continue;
        }

        if dry_run {
            println!(
                "Would apply {} fix(es) to {}",
                result.applied,
                path.display()
            );
            total_applied += result.applied;
            total_files += 1;
            continue;
        }

        check_writable(&path)?;
        fs::write(&path, &result.updated).map_err(|err| {
            eprintln!(
                "error: cannot apply fixes to '{}': {err}",
                path.display()
            );
            ReportedError
        })?;

        total_applied += result.applied;
        total_files += 1;
    }

    if total_applied == 0 {
        if total_overlaps > 0 {
            println!(
                "No fixes applied ({total_overlaps} overlapping suggestion(s) skipped)."
            );
        } else {
            println!("No machine-applicable fixes to apply.");
        }
    } else if dry_run {
        println!(
            "Dry run: would apply {total_applied} fix(es) across {total_files} file(s)."
        );
    } else {
        println!("Applied {total_applied} fix(es) across {total_files} file(s).");
    }

    Ok(CommandOutcome::Success)
}

fn check_writable(path: &Path) -> Result<(), ReportedError> {
    let metadata = fs::metadata(path).map_err(|err| {
        eprintln!("error: failed to inspect '{}': {err}", path.display());
        ReportedError
    })?;
    if metadata.permissions().readonly() {
        eprintln!(
            "error: cannot apply fixes to read-only file '{}'",
            path.display()
        );
        return Err(ReportedError);
    }
    Ok(())
}

pub(crate) fn span_to_byte_range(content: &str, span: Span) -> Option<(usize, usize)> {
    let start = position_to_byte(content, span.start.line, span.start.offset)?;
    let end = position_to_byte(content, span.end.line, span.end.offset)?;
    (start <= end && end <= content.len()).then_some((start, end))
}

fn position_to_byte(content: &str, target_line: usize, target_col: usize) -> Option<usize> {
    let mut line = 0usize;
    let mut byte_idx = 0usize;
    let bytes = content.as_bytes();
    while line < target_line {
        let rel = content[byte_idx..].find('\n')?;
        byte_idx += rel + 1;
        line += 1;
    }
    let line_end = content[byte_idx..]
        .find('\n')
        .map(|rel| byte_idx + rel)
        .unwrap_or(bytes.len());
    let line_slice = &content[byte_idx..line_end];
    let mut col = 0usize;
    for (rel_byte, _) in line_slice.char_indices() {
        if col == target_col {
            return Some(byte_idx + rel_byte);
        }
        col += 1;
    }
    if col == target_col {
        Some(line_end)
    } else {
        None
    }
}

/// Deduplicates identical edits, detects overlapping or conflicting edits
/// (skipping them rather than corrupting source), and applies remaining edits.
pub(crate) fn apply_edits_to_source(content: &str, edits: &[SourceEdit]) -> ApplyResult {
    let mut sorted = edits.to_vec();
    sorted.sort_by(|a, b| {
        a.start_byte
            .cmp(&b.start_byte)
            .then_with(|| a.end_byte.cmp(&b.end_byte))
            .then_with(|| a.replacement.cmp(&b.replacement))
    });

    // Deduplicate identical edits on the same span.
    let mut deduped: Vec<SourceEdit> = Vec::with_capacity(sorted.len());
    for edit in sorted {
        if deduped.last().is_some_and(|prev| {
            prev.start_byte == edit.start_byte
                && prev.end_byte == edit.end_byte
                && prev.replacement == edit.replacement
        }) {
            continue;
        }
        deduped.push(edit);
    }

    let mut accepted: Vec<SourceEdit> = Vec::new();
    let mut skipped_overlaps: Vec<SourceEdit> = Vec::new();

    for edit in deduped {
        if let Some(prev) = accepted.last() {
            let overlaps = if edit.start_byte == edit.end_byte && prev.start_byte == prev.end_byte {
                edit.start_byte == prev.start_byte
            } else {
                edit.start_byte < prev.end_byte
            };
            if overlaps {
                skipped_overlaps.push(edit);
                continue;
            }
        }
        accepted.push(edit);
    }

    let mut updated = content.to_string();
    let applied = accepted.len();
    for edit in accepted.into_iter().rev() {
        updated.replace_range(edit.start_byte..edit.end_byte, &edit.replacement);
    }

    ApplyResult {
        updated,
        applied,
        skipped_overlaps,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use compiler::span::{FileID, Position};

    #[test]
    fn applies_multiple_non_overlapping_edits_and_is_idempotent() {
        let src = "func main() {\n    oldApi()\n    oldApi()\n}\n";
        let e1 = span_to_byte_range(
            src,
            Span {
                start: Position { line: 1, offset: 4 },
                end: Position { line: 1, offset: 10 },
                file: FileID::new(0),
            },
        )
        .unwrap();
        let e2 = span_to_byte_range(
            src,
            Span {
                start: Position { line: 2, offset: 4 },
                end: Position { line: 2, offset: 10 },
                file: FileID::new(0),
            },
        )
        .unwrap();
        let edits = vec![
            SourceEdit {
                start_byte: e1.0,
                end_byte: e1.1,
                line_1_based: 2,
                col_0_based: 4,
                replacement: "newApi".into(),
            },
            SourceEdit {
                start_byte: e2.0,
                end_byte: e2.1,
                line_1_based: 3,
                col_0_based: 4,
                replacement: "newApi".into(),
            },
        ];
        let res = apply_edits_to_source(src, &edits);
        assert_eq!(res.applied, 2);
        assert!(res.skipped_overlaps.is_empty());
        assert_eq!(res.updated, "func main() {\n    newApi()\n    newApi()\n}\n");
    }

    #[test]
    fn skips_overlapping_and_conflicting_edits() {
        let src = "oldCall(x)";
        let edits = vec![
            SourceEdit {
                start_byte: 0,
                end_byte: 7,
                line_1_based: 1,
                col_0_based: 0,
                replacement: "newCall".into(),
            },
            SourceEdit {
                start_byte: 3,
                end_byte: 10,
                line_1_based: 1,
                col_0_based: 3,
                replacement: "other".into(),
            },
            SourceEdit {
                start_byte: 0,
                end_byte: 7,
                line_1_based: 1,
                col_0_based: 0,
                replacement: "altCall".into(),
            },
        ];
        let res = apply_edits_to_source(src, &edits);
        assert_eq!(res.applied, 1);
        assert_eq!(res.skipped_overlaps.len(), 2);
        assert_eq!(res.updated, "altCall(x)");
    }

    #[test]
    fn rejects_read_only_file() {
        let dir = std::env::temp_dir().join(format!("taro-fix-ro-{}", std::process::id()));
        let _ = fs::create_dir_all(&dir);
        let file = dir.join("readonly.tr");
        fs::write(&file, "func main() {}\n").unwrap();
        let mut perms = fs::metadata(&file).unwrap().permissions();
        perms.set_readonly(true);
        fs::set_permissions(&file, perms).unwrap();

        let check = check_writable(&file);
        assert!(check.is_err());

        let mut perms = fs::metadata(&file).unwrap().permissions();
        perms.set_readonly(false);
        let _ = fs::set_permissions(&file, perms);
        let _ = fs::remove_dir_all(&dir);
    }
}
