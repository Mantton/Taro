//! Declaration identities and their current source addresses.

use std::{
    path::PathBuf,
    sync::{
        Arc,
        atomic::{AtomicU64, Ordering},
    },
};

use rustc_hash::FxHashMap;

use crate::{
    hir::{self, DefinitionID, HirVisitor},
    sema::resolve::models::DefinitionKind,
    span::{Position, Span},
};

use super::{
    analysis_products::{
        AnalysisProduct, DeclarationKey, SourceRange, SyntaxUncertainty, TypedOccurrence,
    },
    context::Gcx,
};

/// A declaration's place in the package and its source signature.
#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct DeclarationAnchor {
    pub package: String,
    pub enclosing: Vec<DeclarationComponent>,
    pub declaration: DeclarationComponent,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct DeclarationComponent {
    pub name: String,
    pub kind: DefinitionKind,
    /// Identity of the source header when one is available.
    pub signature: Option<blake3::Hash>,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct DeclarationRecord {
    pub anchor: DeclarationAnchor,
    pub location: DeclarationKey,
}

/// Identifies an unchanged body in a declared function.
#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct BodyIdentity {
    pub owner: DeclarationAnchor,
    pub content: blake3::Hash,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct BodyRecord {
    pub identity: Arc<BodyIdentity>,
    pub declaration: DeclarationKey,
    pub source: SourceRange,
}

/// A traversal position within one unchanged body. Compiler node IDs never
/// cross revisions.
#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct BodyLocalAnchor {
    pub body: Arc<BodyIdentity>,
    pub ordinal: u32,
}

/// A diagnostic or edit range relative to the beginning of its body.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct BodyRelativeRange {
    pub body: Arc<BodyIdentity>,
    pub start: Position,
    pub end: Position,
}

impl BodyRecord {
    pub(crate) fn relative(&self, range: &SourceRange) -> Option<BodyRelativeRange> {
        if self.source.path != range.path
            || range.start > range.end
            || range.start < self.source.start
            || range.end > self.source.end
        {
            return None;
        }
        let relative = |position: Position| {
            let line = position.line - self.source.start.line;
            let offset = if line == 0 {
                position.offset - self.source.start.offset
            } else {
                position.offset
            };
            Position { line, offset }
        };
        Some(BodyRelativeRange {
            body: Arc::clone(&self.identity),
            start: relative(range.start),
            end: relative(range.end),
        })
    }

    fn restore(&self, range: &BodyRelativeRange) -> Option<SourceRange> {
        if self.identity != range.body {
            return None;
        }
        let absolute = |position: Position| {
            let line = self.source.start.line.checked_add(position.line)?;
            let offset = if position.line == 0 {
                self.source.start.offset.checked_add(position.offset)?
            } else {
                position.offset
            };
            Some(Position { line, offset })
        };
        let start = absolute(range.start)?;
        let end = absolute(range.end)?;
        (start <= end && end <= self.source.end).then(|| SourceRange {
            path: self.source.path.clone(),
            start,
            end,
        })
    }
}

/// A stable handle owned by a single declaration tracker.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DeclarationHandle {
    owner: u64,
    serial: u64,
}

/// Current declaration locations and the handles that have stayed valid
/// through every accepted workspace revision.
pub struct DeclarationTracker {
    owner: u64,
    next_serial: u64,
    revision: Option<u64>,
    by_anchor: FxHashMap<DeclarationAnchor, DeclarationHandle>,
    by_handle: FxHashMap<DeclarationHandle, Arc<DeclarationKey>>,
    by_location: FxHashMap<Arc<DeclarationKey>, DeclarationHandle>,
}

impl Default for DeclarationTracker {
    fn default() -> Self {
        static NEXT_TRACKER: AtomicU64 = AtomicU64::new(1);
        let owner = NEXT_TRACKER
            .try_update(Ordering::Relaxed, Ordering::Relaxed, |id| id.checked_add(1))
            .expect("declaration tracker identities exhausted");
        Self {
            owner,
            next_serial: 1,
            revision: None,
            by_anchor: Default::default(),
            by_handle: Default::default(),
            by_location: Default::default(),
        }
    }
}

impl DeclarationTracker {
    pub fn revision(&self) -> Option<u64> {
        self.revision
    }

    /// Reject late replies. If filesystem changes were coalesced, supply files
    /// deleted and recreated since the last accepted revision explicitly.
    pub fn update(&mut self, analysis: &AnalysisProduct, recreated: &[PathBuf]) -> bool {
        if self
            .revision
            .is_some_and(|revision| revision >= analysis.revision)
        {
            return false;
        }
        self.revision = Some(analysis.revision);

        // Group all records before removing uncertain files. A declaration in
        // an uncertain file must still prevent a conflicting match elsewhere.
        let mut unique = FxHashMap::default();
        let mut counts_by_location = FxHashMap::default();
        for record in &analysis.declarations {
            *counts_by_location.entry(&record.location).or_insert(0usize) += 1;
            unique
                .entry(&record.anchor)
                .and_modify(|location| *location = None)
                .or_insert(Some(&record.location));
        }

        let previous_anchors = std::mem::take(&mut self.by_anchor);
        let previous_targets = std::mem::take(&mut self.by_handle);
        self.by_location = FxHashMap::default();
        for (anchor, location) in unique {
            let Some(location) = location else { continue };
            if counts_by_location[location] != 1 {
                continue;
            }
            if match &analysis.syntax_uncertainty {
                SyntaxUncertainty::None => false,
                SyntaxUncertainty::Files(files) => files.contains(&location.source.path),
                SyntaxUncertainty::Package => true,
            } {
                continue;
            }
            let prior = previous_anchors.get(anchor).copied().filter(|handle| {
                previous_targets[handle].source.path == location.source.path
                    && !recreated.contains(&location.source.path)
            });
            let handle = prior.unwrap_or_else(|| {
                let serial = self.next_serial;
                self.next_serial = serial
                    .checked_add(1)
                    .expect("declaration handles exhausted");
                DeclarationHandle {
                    owner: self.owner,
                    serial,
                }
            });
            let location = Arc::new(location.clone());
            self.by_anchor.insert(anchor.clone(), handle);
            self.by_handle.insert(handle, Arc::clone(&location));
            self.by_location.insert(location, handle);
        }
        true
    }

    pub fn handle_for(&self, location: &DeclarationKey) -> Option<DeclarationHandle> {
        self.by_location.get(location).copied()
    }

    pub fn resolve(&self, handle: DeclarationHandle) -> Option<&DeclarationKey> {
        self.by_handle.get(&handle).map(Arc::as_ref)
    }

    /// Move an old range through a still-valid declaration handle and an
    /// unchanged body in the current reply.
    pub fn restore_body_range(
        &self,
        handle: DeclarationHandle,
        range: &BodyRelativeRange,
        current: &AnalysisProduct,
    ) -> Option<SourceRange> {
        self.current_body(handle, current)?.restore(range)
    }

    pub fn restore_occurrence<'a>(
        &self,
        handle: DeclarationHandle,
        anchor: &BodyLocalAnchor,
        current: &'a AnalysisProduct,
    ) -> Option<&'a TypedOccurrence> {
        if self.current_body(handle, current)?.identity != anchor.body {
            return None;
        }
        current
            .occurrences
            .iter()
            .find(|occurrence| occurrence.anchor.as_ref() == Some(anchor))
    }

    fn current_body<'a>(
        &self,
        handle: DeclarationHandle,
        current: &'a AnalysisProduct,
    ) -> Option<&'a BodyRecord> {
        if self.revision != Some(current.revision) {
            return None;
        }
        let target = self.resolve(handle)?;
        current
            .bodies
            .iter()
            .find(|body| body.declaration == *target)
    }
}

/// The compiler's local definition IDs are used only while collecting this map.
pub(crate) fn collect(
    gcx: Gcx<'_>,
    package: &hir::Package,
) -> FxHashMap<DefinitionID, DeclarationRecord> {
    let mut declarations = HeaderSites {
        gcx,
        signatures: FxHashMap::default(),
    };
    hir::walk_package(&mut declarations, package);
    gcx.resolution_output(gcx.package_index())
        .definition_to_ident
        .keys()
        .filter_map(|&id| declarations.capture(id).map(|record| (id, record)))
        .collect()
}

pub(super) fn collect_function(
    gcx: Gcx<'_>,
    id: DefinitionID,
    function: &hir::Function,
) -> Option<DeclarationRecord> {
    let mut headers = HeaderSites {
        gcx,
        signatures: FxHashMap::default(),
    };
    headers.record(id, [function.signature.span]);
    headers.capture(id)
}

struct HeaderSites<'ctx> {
    gcx: Gcx<'ctx>,
    signatures: FxHashMap<DefinitionID, blake3::Hash>,
}

impl HeaderSites<'_> {
    fn capture(&self, id: DefinitionID) -> Option<DeclarationRecord> {
        let gcx = self.gcx;
        let output = gcx.resolution_output(gcx.package_index());
        let component = |id| {
            let kind = *output.definition_to_kind.get(&id)?;
            let name = output
                .definition_to_ident
                .get(&id)
                .map(|ident| gcx.symbol_text(ident.symbol).into())
                .unwrap_or_default();
            Some(DeclarationComponent {
                name,
                kind,
                signature: self.signatures.get(&id).copied(),
            })
        };
        let location = DeclarationKey::capture(gcx, id)?;
        if location.name.is_empty() || location.source.start == location.source.end {
            return None;
        }
        let mut enclosing = Vec::new();
        let mut current = id;
        while let Some(&parent) = output.definition_to_parent.get(&current) {
            enclosing.push(component(parent)?);
            current = parent;
        }
        enclosing.reverse();
        let anchor = DeclarationAnchor {
            package: location.package.clone(),
            enclosing,
            declaration: component(id)?,
        };
        Some(DeclarationRecord { anchor, location })
    }

    fn record(&mut self, id: DefinitionID, pieces: impl IntoIterator<Item = Span>) {
        let mut hash = blake3::Hasher::new();
        for piece in pieces {
            let Some(source) = self.gcx.dcx().source_text(piece) else {
                return;
            };
            hash.update(&(source.len() as u64).to_le_bytes());
            hash.update(source.as_bytes());
        }
        self.signatures.insert(id, hash.finalize());
    }
}

impl HirVisitor for HeaderSites<'_> {
    fn visit_function(
        &mut self,
        id: DefinitionID,
        node: &hir::Function,
        context: hir::FunctionContext,
    ) {
        self.record(id, [node.signature.span]);
        hir::walk_function(self, id, node, context);
    }

    fn visit_impl(&mut self, node: &hir::Impl, id: DefinitionID) {
        self.record(
            id,
            std::iter::once(node.target.span)
                .chain(node.interface.iter().map(|interface| interface.span))
                .chain(
                    node.generics
                        .type_parameters
                        .iter()
                        .map(|parameters| parameters.span),
                )
                .chain(node.generics.where_clause.iter().map(|clause| clause.span))
                .chain(node.delegate.iter().map(|delegate| delegate.span)),
        );
        hir::walk_impl(self, node, id);
    }
}

#[cfg(test)]
mod tests {
    use super::{AnalysisProduct, DeclarationKey, DeclarationTracker, TypedOccurrence};
    use crate::{
        compile::source::{FileContents, FileOverlay, SourceText, WorkspaceSources},
        test_support::{TempDir, with_lint_warnings, with_workspace_compiler},
    };
    use std::{path::Path, rc::Rc, sync::Arc};

    fn analyze(root: &Path, revision: u64, files: &[(&str, &str)]) -> AnalysisProduct {
        let changes = files.iter().map(|(name, text)| {
            let source = SourceText::new((*text).into());
            (
                root.join("src").join(name),
                FileOverlay::Contents(FileContents::Text(Arc::new(source))),
            )
        });
        let sources = Rc::new(WorkspaceSources::new(revision, changes).unwrap());
        let reply = with_workspace_compiler(root, sources, None, |compiler| {
            compiler.analyze_owned(revision)
        });
        assert!(reply.complete, "{:?}", reply.diagnostics);
        reply
    }

    fn direct_overload(reply: &AnalysisProduct) -> &DeclarationKey {
        reply
            .occurrences
            .iter()
            .filter(|fact| {
                fact.source.start.line == 2 && fact.source.path.ends_with("src/calls.tr")
            })
            .filter_map(|fact| fact.declaration.as_ref())
            .find(|decl| decl.name == "label")
            .expect("destination of direct label call")
    }

    #[test]
    fn declaration_handles_follow_overloads_and_reject_replacements() {
        let root = TempDir::new("declaration-identity");
        let dispatch = include_str!("analysis_oracle/dispatch.tr");
        let calls = include_str!("analysis_oracle/calls.tr");
        let check = |revision, source: &str| {
            analyze(
                &root,
                revision,
                &[("dispatch.tr", source), ("calls.tr", calls)],
            )
        };
        let original = check(1, dispatch);
        let original_location = direct_overload(&original);
        let mut tracker = DeclarationTracker::default();
        assert!(tracker.update(&original, &[]));
        let handle = tracker
            .handle_for(original_location)
            .expect("unique overload handle");

        let first = "    func label(_ n: bool) -> int32 { 32 }";
        let second = "    func label(_ n: string) -> int32 { 64 }";
        let moved = dispatch.replace(&format!("{first}\n{second}"), &format!("{second}\n{first}"));
        let moved = format!("// Shift declarations.\nstruct Inserted {{}}\n{moved}");
        let revised = check(2, &moved);
        let revised_location = direct_overload(&revised);
        assert_eq!(
            revised_location.source.start.line,
            original_location.source.start.line + 3
        );
        assert!(tracker.update(&revised, &[]));
        assert_eq!(tracker.handle_for(revised_location), Some(handle));
        assert_eq!(tracker.resolve(handle), Some(revised_location));
        assert!(!tracker.update(&original, &[]));

        let mut ambiguous = revised.clone();
        ambiguous.revision = 3;
        let duplicate = ambiguous
            .declarations
            .iter()
            .find(|decl| decl.location == *revised_location)
            .unwrap()
            .clone();
        ambiguous.declarations.push(duplicate);
        assert!(tracker.update(&ambiguous, &[]));
        assert!(tracker.resolve(handle).is_none());

        let resolved = check(4, &moved);
        assert!(tracker.update(&resolved, &[]));
        let resolved_handle = tracker.handle_for(direct_overload(&resolved)).unwrap();
        assert_ne!(resolved_handle, handle);
        let deleted = analyze(&root, 5, &[("remaining.tr", "func other() {}")]);
        assert!(tracker.update(&deleted, &[]));
        assert!(tracker.resolve(resolved_handle).is_none());
        let recreated = check(6, &moved);
        assert!(tracker.update(&recreated, &[]));
        let recreated_location = direct_overload(&recreated);
        let recreated_handle = tracker.handle_for(recreated_location).unwrap();
        assert_ne!(recreated_handle, resolved_handle);

        let coalesced = check(7, &moved);
        assert!(tracker.update(&coalesced, &[recreated_location.source.path.clone()]));
        assert!(tracker.resolve(recreated_handle).is_none());
        let replacement_handle = tracker.handle_for(direct_overload(&coalesced)).unwrap();
        let sibling = coalesced
            .declarations
            .iter()
            .find(|decl| decl.location.name == "useDispatch")
            .unwrap();
        let sibling_handle = tracker.handle_for(&sibling.location).unwrap();
        let mut uncertain = coalesced.clone();
        uncertain.revision = 8;
        uncertain.syntax_uncertainty = super::SyntaxUncertainty::Files(
            vec![recreated_location.source.path.clone()].into_boxed_slice(),
        );
        assert!(tracker.update(&uncertain, &[]));
        assert!(tracker.resolve(replacement_handle).is_none());
        assert_eq!(tracker.resolve(sibling_handle), Some(&sibling.location));
        let mut another_tracker = DeclarationTracker::default();
        assert!(another_tracker.update(&recreated, &[]));
        assert!(another_tracker.resolve(recreated_handle).is_none());
    }

    fn local_use(reply: &AnalysisProduct, line: usize) -> &TypedOccurrence {
        reply
            .occurrences
            .iter()
            .find(|fact| fact.source.start.line == line && fact.local_declaration.is_some())
            .expect("local variable use")
    }

    #[test]
    fn rebinds_body_anchors_and_diagnostic_ranges_after_a_shift() {
        let root = TempDir::new("body-identity");
        let body = "func inspect() -> int32 {\n\
                    var value: int32 = 1\n\
                    dormant := value\n\
                    inner := {\n\
                    var value: int32 = 2\n\
                    value\n\
                    }\n\
                    return value\n\
                    }";
        let check = |revision, source: &str| {
            with_lint_warnings(|| analyze(&root, revision, &[("body.tr", source)]))
        };
        let original = check(1, body);
        let outer = local_use(&original, 2);
        let inner = local_use(&original, 5);
        assert_eq!(
            outer.local_declaration.as_ref().unwrap().source.start.line,
            1
        );
        assert_eq!(
            inner.local_declaration.as_ref().unwrap().source.start.line,
            4
        );
        assert_ne!(
            outer.local_declaration.as_ref().unwrap().anchor,
            inner.local_declaration.as_ref().unwrap().anchor
        );
        let diagnostic = original
            .diagnostics
            .iter()
            .find(|diag| diag.message.contains("dormant"))
            .unwrap();
        let range = diagnostic.body_range.as_ref().unwrap();

        let mut tracker = DeclarationTracker::default();
        assert!(tracker.update(&original, &[]));
        let handle = tracker.handle_for(&original.bodies[0].declaration).unwrap();
        let shifted = format!("// Line shift.\nstruct Extra {{}}\n{body}");
        let revised = check(2, &shifted);
        assert!(tracker.update(&revised, &[]));
        let moved = tracker
            .restore_occurrence(handle, outer.anchor.as_ref().unwrap(), &revised)
            .unwrap();
        assert_eq!(moved, local_use(&revised, 4));
        assert_eq!(
            moved.local_declaration.as_ref().unwrap().source.start.line,
            3
        );
        let updated_diagnostic = revised
            .diagnostics
            .iter()
            .find(|diag| diag.message.contains("dormant"))
            .unwrap();
        assert_eq!(
            tracker.restore_body_range(handle, range, &revised),
            updated_diagnostic.source
        );

        let changed = check(3, &shifted.replace("= 2", "= 3"));
        assert!(tracker.update(&changed, &[]));
        assert!(tracker.resolve(handle).is_some());
        assert!(
            tracker
                .restore_occurrence(handle, outer.anchor.as_ref().unwrap(), &changed)
                .is_none()
        );
        assert!(
            tracker
                .restore_body_range(handle, range, &changed)
                .is_none()
        );
    }
}
