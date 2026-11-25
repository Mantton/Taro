//! Per-package source observations collected during placement and emission.
//! Cached code replays the same sorted entries without rerunning the optimizer.
use super::context::Gcx;
use crate::span::Span;
use serde::{Deserialize, Serialize};
use std::{
    collections::BTreeSet,
    path::{Path, PathBuf},
};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub(crate) struct AllocationNote {
    file: PathBuf,
    line: usize,
    column: usize,
    message: String,
}
pub(crate) type AllocationReport = BTreeSet<AllocationNote>;

impl<'ctx> Gcx<'ctx> {
    pub fn begin_allocation_report(self, enabled: bool) {
        self.store
            .allocation_report
            .replace(enabled.then(BTreeSet::new));
    }

    pub(crate) fn explains_allocations(self) -> bool {
        self.store.allocation_report.borrow().is_some()
    }

    fn report_source_root(self) -> &'ctx Path {
        if self.config.is_script {
            self.config.src.parent().unwrap_or(&self.config.src)
        } else {
            &self.config.src
        }
    }

    pub(crate) fn allocation_location(self, span: Span) -> String {
        let file = self.dcx.file_path(span.file).unwrap_or_default();
        let path = file
            .strip_prefix(self.report_source_root())
            .unwrap_or(&file);
        let location = format!(
            "{}:{}:{}",
            path.display(),
            span.start.line + 1,
            span.start.offset + 1
        );
        if span.start.line == span.end.line
            && span.end.offset.saturating_sub(span.start.offset) <= 80
            && let Some(text) = self.dcx.source_text(span)
            && !text.is_empty()
            && !text.chars().any(char::is_control)
        {
            return format!("{location} (`{text}`)");
        }
        location
    }

    pub(crate) fn record_allocation(self, span: Span, message: String) {
        if span.start == span.end {
            return;
        }
        let Some(path) = self.dcx.file_path(span.file) else {
            return;
        };
        if let Some(report) = self.store.allocation_report.borrow_mut().as_mut() {
            report.insert(AllocationNote {
                file: path
                    .strip_prefix(self.report_source_root())
                    .unwrap_or(&path)
                    .to_owned(),
                line: span.start.line + 1,
                column: span.start.offset + 1,
                message,
            });
        }
    }

    pub fn print_allocation_report(self) {
        let Some(report) = self.store.allocation_report.take() else {
            return;
        };
        let cwd = std::env::current_dir().ok();
        for note in report {
            let path = self.report_source_root().join(note.file);
            let shown = cwd
                .as_ref()
                .and_then(|root| path.strip_prefix(root).ok())
                .unwrap_or(&path);
            eprintln!(
                "{}:{}:{}: allocation: {}",
                shown.display(),
                note.line,
                note.column,
                note.message
            );
        }
    }
}
