//! Bounded storage of owned products for one active package.

use std::sync::atomic::{AtomicBool, Ordering};

use indexmap::IndexMap;
use rustc_hash::FxBuildHasher;

use super::{
    analysis_products::{
        AnalysisDiagnostic, Argument, ConstantArgument, ConstantArgumentValue, DeclarationKey,
        OwnedConstant, SourceRange, TypeShape,
    },
    body_check::BodyProduct,
    declarations::{BodyRecord, DeclarationHandle, DeclarationTracker},
};
use crate::span::Position;

/// The current declaration and body obtained from the edited syntax. The
/// caller must have checked package membership and dependency fingerprints
/// before accepting the revision.
pub struct BodyCacheRequest<'a> {
    pub revision: u64,
    pub handle: DeclarationHandle,
    pub body: &'a BodyRecord,
    pub scope: &'a SourceRange,
}

/// A package's latest body products. Encoded entries own exact-sized buffers,
/// so repeated replacements cannot retain spare capacity inside a product.
/// Lookups return independent products that can outlive the cache entry.
pub struct BodyCache {
    limit: usize,
    payload_bytes: usize,
    revision: Option<u64>,
    fingerprint: Option<blake3::Hash>,
    entries: IndexMap<DeclarationHandle, Box<[u8]>, FxBuildHasher>,
}

// Allow for the key, boxed slice, and the hash table's buckets and control
// bytes. The body lengths themselves are exact.
const RETAINED_BYTES_PER_BUCKET: usize = 128;

impl BodyCache {
    pub fn new(max_bytes: usize) -> Self {
        Self {
            limit: max_bytes,
            payload_bytes: 0,
            revision: None,
            fingerprint: None,
            entries: IndexMap::default(),
        }
    }

    pub fn retained_bytes(&self) -> usize {
        self.payload_bytes.saturating_add(
            self.entries
                .capacity()
                .saturating_mul(RETAINED_BYTES_PER_BUCKET),
        )
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Accept only newer revisions with a matching, current declaration map.
    /// Pass the handles whose body inputs changed or whose source was damaged.
    /// A missing fingerprint retires all products before any new lookup.
    pub fn advance(
        &mut self,
        revision: u64,
        fingerprint: Option<blake3::Hash>,
        tracker: &DeclarationTracker,
        invalidated: &[DeclarationHandle],
    ) -> bool {
        if tracker.revision() != Some(revision)
            || self.revision.is_some_and(|current| current >= revision)
        {
            return false;
        }
        if self.fingerprint != fingerprint || fingerprint.is_none() {
            self.entries = IndexMap::default();
            self.payload_bytes = 0;
        } else {
            for &handle in invalidated {
                self.remove(handle);
            }
            let payload_bytes = &mut self.payload_bytes;
            self.entries.retain(|handle, bytes| {
                if tracker.resolve(*handle).is_some() {
                    return true;
                }
                *payload_bytes -= bytes.len();
                false
            });
            self.shrink_if_sparse();
        }
        self.revision = Some(revision);
        self.fingerprint = fingerprint;
        true
    }

    pub fn get(
        &mut self,
        tracker: &DeclarationTracker,
        request: &BodyCacheRequest<'_>,
    ) -> Option<BodyProduct> {
        let fingerprint = self.accepts(tracker, request)?;
        let bytes = self.entries.get(&request.handle)?;
        let product = bincode::deserialize::<BodyProduct>(bytes)
            .ok()
            .and_then(|mut product| {
                if product.package_fingerprint != fingerprint
                    || product.body.identity != request.body.identity
                    || product.scope.path != request.scope.path
                {
                    return None;
                }
                relocate(&mut product, request.scope)?;
                (product.body == *request.body
                    && product.declaration.location == request.body.declaration)
                    .then_some(product)
            });
        if product.is_none() {
            self.remove(request.handle);
            self.shrink_if_sparse();
        }
        product
    }

    /// Install a complete body result. Revision validity, identity and
    /// cancellation are checked before an entry becomes visible to readers.
    /// Non-local navigation destinations require a package check for now.
    pub fn publish(
        &mut self,
        tracker: &DeclarationTracker,
        request: &BodyCacheRequest<'_>,
        mut product: BodyProduct,
        cancelled: &AtomicBool,
    ) -> bool {
        let Some(fingerprint) = self.accepts(tracker, request) else {
            return false;
        };
        if cancelled.load(Ordering::Acquire)
            || product.package_fingerprint != fingerprint
            || product.body != *request.body
            || product.declaration.location != request.body.declaration
            || product.declaration.anchor != request.body.identity.owner
            || product.scope != *request.scope
            || relocate(&mut product, request.scope).is_none()
        {
            return false;
        }
        let Some(size) = bincode::serialized_size(&product)
            .ok()
            .and_then(|size| usize::try_from(size).ok())
        else {
            return false;
        };
        if size.saturating_add(RETAINED_BYTES_PER_BUCKET) > self.limit {
            return false;
        }
        let mut encoded = Vec::with_capacity(size);
        if bincode::serialize_into(&mut encoded, &product).is_err()
            || cancelled.load(Ordering::Acquire)
        {
            return false;
        }
        self.remove(request.handle);
        self.payload_bytes += encoded.len();
        self.entries
            .insert(request.handle, encoded.into_boxed_slice());
        while self.retained_bytes() > self.limit {
            self.payload_bytes -= self.entries.shift_remove_index(0).unwrap().1.len();
            self.entries.shrink_to_fit();
        }
        self.entries.contains_key(&request.handle)
    }

    fn accepts(
        &self,
        tracker: &DeclarationTracker,
        request: &BodyCacheRequest<'_>,
    ) -> Option<blake3::Hash> {
        let revision = Some(request.revision);
        if self.revision != revision
            || tracker.revision() != revision
            || tracker.handle_for(&request.body.declaration) != Some(request.handle)
            || request.body.source.path != request.scope.path
            || request.body.source.start < request.scope.start
            || request.body.source.end > request.scope.end
        {
            return None;
        }
        self.fingerprint
    }

    fn remove(&mut self, handle: DeclarationHandle) {
        if let Some(removed) = self.entries.shift_remove(&handle) {
            self.payload_bytes -= removed.len();
        }
    }

    fn shrink_if_sparse(&mut self) {
        if self.entries.len() <= self.entries.capacity() / 4 {
            self.entries.shrink_to_fit();
        }
    }
}

/// Rebase through the current scope. A product containing a destination
/// outside this scope needs a different relocation proof.
fn relocate(product: &mut BodyProduct, to: &SourceRange) -> Option<()> {
    let map = |range: &mut SourceRange| {
        *range = move_range(range, &product.scope, to)?;
        Some(())
    };
    if move_range(&product.scope, &product.scope, to)? != *to {
        return None;
    }
    map(&mut product.declaration.location.source)?;
    map(&mut product.body.declaration.source)?;
    map(&mut product.body.source)?;
    for occurrence in &mut product.occurrences {
        map(&mut occurrence.source)?;
        if let Some(local) = &mut occurrence.local_declaration {
            map(&mut local.source)?;
        }
        if let Some(declaration) = &mut occurrence.declaration {
            map(&mut declaration.source)?;
        }
        move_types(&mut occurrence.ty, &map)?;
    }
    for diagnostic in &mut product.diagnostics {
        move_diagnostic(diagnostic, &map)?;
    }
    product.scope = to.clone();
    Some(())
}

fn move_range(range: &SourceRange, from: &SourceRange, to: &SourceRange) -> Option<SourceRange> {
    if range.path != from.path
        || range.start < from.start
        || range.end > from.end
        || range.start > range.end
    {
        return None;
    }
    let position = |position: Position| {
        let line = position.line.checked_sub(from.start.line)?;
        let offset = if line == 0 {
            to.start
                .offset
                .checked_add(position.offset.checked_sub(from.start.offset)?)?
        } else {
            position.offset
        };
        Some(Position {
            line: to.start.line.checked_add(line)?,
            offset,
        })
    };
    let start = position(range.start)?;
    let end = position(range.end)?;
    (end <= to.end).then(|| SourceRange {
        path: to.path.clone(),
        start,
        end,
    })
}

type MoveRange<'a> = dyn Fn(&mut SourceRange) -> Option<()> + 'a;

fn move_diagnostic(diagnostic: &mut AnalysisDiagnostic, map: &MoveRange<'_>) -> Option<()> {
    if let Some(source) = &mut diagnostic.source {
        map(source)?;
    } else {
        return None;
    }
    if let Some(suggestion) = &mut diagnostic.suggestion {
        map(&mut suggestion.source)?;
    }
    for note in &mut diagnostic.notes {
        move_diagnostic(note, map)?;
    }
    Some(())
}

fn move_types(ty: &mut TypeShape, map: &MoveRange<'_>) -> Option<()> {
    let declaration = |key: &mut Option<DeclarationKey>| {
        if let Some(key) = key {
            map(&mut key.source)?;
        }
        Some(())
    };
    let args = |arguments: &mut [Argument]| {
        for argument in arguments {
            match argument {
                Argument::Type(ty) => move_types(ty, map)?,
                Argument::Constant(argument) => move_constant_argument(argument, map)?,
            }
        }
        Some(())
    };
    match ty {
        TypeShape::Nominal {
            declaration: key,
            arguments,
            ..
        }
        | TypeShape::Alias {
            declaration: key,
            arguments,
            ..
        } => {
            declaration(key)?;
            args(arguments)?;
        }
        TypeShape::Closure {
            declaration: key,
            arguments,
            inputs,
            output,
            ..
        } => {
            declaration(key)?;
            args(arguments)?;
            for input in inputs {
                move_types(input, map)?;
            }
            move_types(output, map)?;
        }
        TypeShape::Function { inputs, output, .. } => {
            for input in inputs {
                move_types(input, map)?;
            }
            move_types(output, map)?;
        }
        TypeShape::Interfaces(interfaces) => {
            for interface in interfaces {
                declaration(&mut interface.declaration)?;
                args(&mut interface.arguments)?;
                for (_, binding) in &mut interface.bindings {
                    move_types(binding, map)?;
                }
            }
        }
        TypeShape::Array { element, len } => {
            move_types(element, map)?;
            move_constant_argument(len, map)?;
        }
        TypeShape::Tuple(elements) => {
            for element in elements {
                move_types(&mut element.ty, map)?;
            }
        }
        TypeShape::Pointer(ty, _) | TypeShape::Reference(ty) => move_types(ty, map)?,
        TypeShape::Opaque(key) => declaration(key)?,
        TypeShape::Bool
        | TypeShape::Rune
        | TypeShape::String
        | TypeShape::Int(_)
        | TypeShape::UInt(_)
        | TypeShape::Float(_)
        | TypeShape::Parameter { .. }
        | TypeShape::ExistentialSelf(_)
        | TypeShape::Unresolved
        | TypeShape::Error
        | TypeShape::Never => {}
    }
    Some(())
}

fn move_constant_argument(argument: &mut ConstantArgument, map: &MoveRange<'_>) -> Option<()> {
    move_types(&mut argument.ty, map)?;
    if let ConstantArgumentValue::Literal(value) = &mut argument.value {
        move_constant(value, map)?;
    }
    Some(())
}

fn move_constant(value: &mut OwnedConstant, map: &MoveRange<'_>) -> Option<()> {
    match value {
        OwnedConstant::EnumUnitVariant(declaration) => map(&mut declaration.source)?,
        OwnedConstant::Array(elements) => {
            for value in elements {
                move_constant(value, map)?;
            }
        }
        OwnedConstant::Bytes(_)
        | OwnedConstant::Integer(_)
        | OwnedConstant::Bool(_)
        | OwnedConstant::Rune(_)
        | OwnedConstant::String(_)
        | OwnedConstant::FloatBits(_)
        | OwnedConstant::Unit => {}
    }
    Some(())
}

#[cfg(test)]
mod tests {
    use super::{BodyCache, BodyCacheRequest, BodyProduct, DeclarationTracker};
    use crate::{
        compile::{
            Compiler,
            analysis_products::AnalysisProduct,
            source::{FileContents, FileOverlay, SourceText, WorkspaceSources},
        },
        span::Position,
        test_support::{TempDir, with_lint_warnings, with_workspace_compiler},
    };
    use std::{
        path::Path,
        rc::Rc,
        sync::{Arc, atomic::AtomicBool},
    };

    const BODY: &str =
        "func local(_ x: int32) -> int32 {\n    unused := true\n    run := () => x\n    run()\n}";
    const PRECEDING: &str = "func another() -> int32 { 1 }\n";

    fn with_source<R>(
        root: &Path,
        revision: u64,
        source: &str,
        check: impl for<'ctx> FnOnce(&mut Compiler<'ctx>) -> R,
    ) -> R {
        let content = FileContents::Text(Arc::new(SourceText::new(source.into())));
        let sources = WorkspaceSources::new(
            revision,
            [(root.join("src/file.tr"), FileOverlay::Contents(content))],
        )
        .unwrap();
        with_lint_warnings(|| with_workspace_compiler(root, Rc::new(sources), None, check))
    }

    fn run(
        root: &Path,
        revision: u64,
        source: &str,
        line: usize,
    ) -> (AnalysisProduct, BodyProduct) {
        let eager = with_source(root, revision, source, |compiler| {
            compiler.analyze_owned(revision)
        });
        assert!(eager.complete, "{:?}", eager.diagnostics);
        let body = with_source(root, revision, source, |compiler| {
            compiler
                .check_body_owned(
                    &root.join("src/file.tr"),
                    Position { line, offset: 0 },
                    None,
                )
                .unwrap()
        });
        (eager, body)
    }

    fn request<'a>(
        revision: u64,
        tracker: &DeclarationTracker,
        product: &'a BodyProduct,
    ) -> BodyCacheRequest<'a> {
        BodyCacheRequest {
            revision,
            handle: tracker.handle_for(&product.declaration.location).unwrap(),
            body: &product.body,
            scope: &product.scope,
        }
    }

    #[test]
    fn unchanged_body_relocates_local_and_closure_destinations_and_warnings() {
        let root = TempDir::new("cached-body-relocation");
        let mut tracker = DeclarationTracker::default();
        let mut cache = BodyCache::new(32 * 1024);
        let (eager, first) = run(&root, 1, &format!("{PRECEDING}{BODY}"), 1);
        assert!(tracker.update(&eager, &[]));
        assert!(cache.advance(1, Some(first.package_fingerprint), &tracker, &[]));
        let initial = request(1, &tracker, &first);
        let pending = AtomicBool::new(false);
        assert!(cache.publish(&tracker, &initial, first.clone(), &pending));
        let retained = cache.retained_bytes();
        let held_result = cache.get(&tracker, &initial).unwrap();

        let (eager, moved) = run(
            &root,
            2,
            &format!("func another() -> int32 {{\n    2\n}}\n{BODY}"),
            3,
        );
        assert_eq!(moved.package_fingerprint, first.package_fingerprint);
        assert!(tracker.update(&eager, &[]));
        assert!(cache.advance(2, Some(moved.package_fingerprint), &tracker, &[]));
        assert!(cache.get(&tracker, &initial).is_none());
        assert!(!cache.publish(&tracker, &initial, first.clone(), &pending));
        assert_eq!(
            cache.get(&tracker, &request(2, &tracker, &moved)),
            Some(moved.clone())
        );
        assert_eq!(cache.retained_bytes(), retained);
        assert_eq!(held_result, first);

        let changed = BODY.replace("unused := true", "unused := 7");
        let (eager, changed) = run(&root, 3, &format!("{PRECEDING}{changed}"), 1);
        assert_eq!(changed.package_fingerprint, first.package_fingerprint);
        assert!(tracker.update(&eager, &[]));
        assert!(cache.advance(
            3,
            Some(changed.package_fingerprint),
            &tracker,
            &[initial.handle]
        ));
        assert_eq!(cache.retained_bytes(), 0);
        let replacement = request(3, &tracker, &changed);
        pending.store(true, std::sync::atomic::Ordering::Release);
        assert!(!cache.publish(&tracker, &replacement, changed.clone(), &pending));
        assert!(cache.get(&tracker, &replacement).is_none());
    }

    #[test]
    fn byte_limit_evicts_entries_and_recreated_declarations_release_keys() {
        let root = TempDir::new("cached-body-capacity");
        let local = "unread".repeat(180);
        let make_function = |name| format!("func {name}() {{ {local} := 1 }}");
        let source = format!("{}\n{}\n", make_function("first"), make_function("again"));
        let (eager, first) = run(&root, 1, &source, 0);
        let (_, second) = run(&root, 1, &source, 1);
        let max_payload = bincode::serialized_size(&first)
            .unwrap()
            .max(bincode::serialized_size(&second).unwrap()) as usize;
        let limit = max_payload + 1024;
        let mut tracker = DeclarationTracker::default();
        let mut cache = BodyCache::new(limit);
        tracker.update(&eager, &[]);
        cache.advance(1, Some(first.package_fingerprint), &tracker, &[]);
        let first_request = request(1, &tracker, &first);
        let second_request = request(1, &tracker, &second);
        let pending = AtomicBool::new(false);
        assert!(cache.publish(&tracker, &first_request, first.clone(), &pending));
        assert!(cache.publish(&tracker, &second_request, second.clone(), &pending));
        assert_eq!(cache.len(), 1);
        assert!(cache.retained_bytes() <= limit);
        assert!(cache.get(&tracker, &first_request).is_none());
        assert_eq!(cache.get(&tracker, &second_request), Some(second));

        let (eager, recreated) = run(&root, 2, &source, 0);
        tracker.update(&eager, std::slice::from_ref(&recreated.scope.path));
        cache.advance(2, Some(recreated.package_fingerprint), &tracker, &[]);
        assert!(cache.is_empty());
        assert_eq!(cache.retained_bytes(), 0);
    }

    #[test]
    fn a_cross_body_destination_has_no_local_relocation_proof() {
        let root = TempDir::new("cached-body-nonlocal");
        let (eager, body) = run(
            &root,
            1,
            "func source() -> int32 { 1 }\nfunc read() -> int32 { source() }",
            1,
        );
        let mut tracker = DeclarationTracker::default();
        let mut cache = BodyCache::new(32 * 1024);
        tracker.update(&eager, &[]);
        cache.advance(1, Some(body.package_fingerprint), &tracker, &[]);
        let request = request(1, &tracker, &body);
        assert!(!cache.publish(&tracker, &request, body.clone(), &AtomicBool::new(false)));
        assert!(cache.is_empty());
    }
}
