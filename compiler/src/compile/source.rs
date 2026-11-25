//! Inputs read by the parser, diagnostics and compile-time evaluation.

use std::{
    cell::RefCell,
    collections::BTreeMap,
    ffi::OsString,
    fs, io,
    ops::Range,
    path::{Path, PathBuf},
    sync::{
        Arc, OnceLock,
        atomic::{AtomicU64, Ordering},
    },
};

use line_index::{LineCol, LineIndex, TextSize, WideEncoding, WideLineCol};
use rustc_hash::FxHashMap;

use crate::span::Position;

/// Immutable text and its lazily shared line index.
#[derive(Debug)]
pub struct SourceText {
    text: String,
    lines: OnceLock<LineIndex>,
}

/// A document position whose column counts UTF-16 code units.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Utf16Position {
    pub line: u32,
    pub column: u32,
}

impl SourceText {
    pub fn new(text: String) -> Self {
        Self {
            text,
            lines: OnceLock::new(),
        }
    }

    pub fn text(&self) -> &str {
        &self.text
    }

    /// Convert the compiler's Unicode-scalar position to an original byte offset.
    pub fn byte_offset(&self, position: Position) -> Option<usize> {
        let line = u32::try_from(position.line).ok()?;
        let col = u32::try_from(position.offset).ok()?;
        self.wide_offset(WideEncoding::Utf32, WideLineCol { line, col })
    }

    pub fn scalar_position(&self, byte: usize) -> Option<Position> {
        let index = self.line_index()?;
        let coords = index.try_line_col(TextSize::try_from(byte).ok()?)?;
        if byte > self.line_content(coords.line)?.end {
            return None;
        }
        let wide = index.to_wide(WideEncoding::Utf32, coords)?;
        Some(Position {
            line: wide.line as usize,
            offset: wide.col as usize,
        })
    }

    pub fn to_utf16(&self, position: Position) -> Option<Utf16Position> {
        let index = self.line_index()?;
        let offset = TextSize::try_from(self.byte_offset(position)?).ok()?;
        let coords = index.try_line_col(offset)?;
        let wide = index.to_wide(WideEncoding::Utf16, coords)?;
        Some(Utf16Position {
            line: wide.line,
            column: wide.col,
        })
    }

    /// Convert an editor position. Columns beyond a line's end are clamped.
    /// Offsets between the halves of a surrogate pair are invalid.
    pub fn from_utf16(&self, position: Utf16Position) -> Option<Position> {
        let index = self.line_index()?;
        let range = self.line_content(position.line)?;
        let end = index.to_wide(
            WideEncoding::Utf16,
            LineCol {
                line: position.line,
                col: u32::try_from(range.len()).ok()?,
            },
        )?;
        let byte = self.wide_offset(
            WideEncoding::Utf16,
            WideLineCol {
                line: position.line,
                col: position.column.min(end.col),
            },
        )?;
        self.scalar_position(byte)
    }

    fn line_index(&self) -> Option<&LineIndex> {
        (self.text.len() < u32::MAX as usize)
            .then(|| self.lines.get_or_init(|| LineIndex::new(&self.text)))
    }

    /// Bounds excluding the newline sequence. The lexer normalizes CRLF
    /// to LF before it creates scalar positions.
    fn line_content(&self, line: u32) -> Option<Range<usize>> {
        let range: Range<usize> = self.line_index()?.line(line)?.into();
        let line = self.text.get(range.clone())?;
        let content = line
            .strip_suffix("\r\n")
            .or_else(|| line.strip_suffix('\n'))
            .unwrap_or(line);
        Some(range.start..range.start + content.len())
    }

    fn wide_offset(&self, encoding: WideEncoding, position: WideLineCol) -> Option<usize> {
        let range = self.line_content(position.line)?;
        let coords = self.line_index()?.to_utf8(encoding, position)?;
        if coords.col as usize > range.len() {
            return None;
        }
        let offset = range.start + coords.col as usize;
        self.text.is_char_boundary(offset).then_some(offset)
    }
}

/// An input's bytes, with a shared text view for UTF-8 files.
#[derive(Debug, Clone)]
pub enum FileContents {
    Text(Arc<SourceText>),
    Binary(Arc<[u8]>),
}

impl FileContents {
    pub fn as_bytes(&self) -> &[u8] {
        match self {
            Self::Text(source) => source.text().as_bytes(),
            Self::Binary(bytes) => bytes,
        }
    }

    pub fn into_text(self) -> io::Result<Arc<SourceText>> {
        match self {
            Self::Text(source) => Ok(source),
            Self::Binary(_) => Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "file contents are not valid UTF-8",
            )),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EntryKind {
    File,
    Directory,
}

#[derive(Debug, Clone)]
pub struct DirectoryEntry {
    pub path: PathBuf,
    pub kind: EntryKind,
}

/// Identity and revision of a tracked source view.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SourceVersion {
    owner: u64,
    revision: u64,
}

/// The source provider's attestation that only this text changed.
pub struct SingleFileEdit {
    pub(super) previous: SourceVersion,
    pub(super) path: PathBuf,
}

/// The compiler's view of a set of files. Paths returned from directory
/// enumeration can be passed directly to read or resolve.
pub trait SourceProvider {
    fn resolve(&self, path: &Path) -> io::Result<PathBuf>;
    fn read_directory(&self, path: &Path) -> io::Result<Vec<DirectoryEntry>>;
    fn read_file(&self, path: &Path) -> io::Result<FileContents>;

    fn workspace_revision(&self) -> Option<u64> {
        None
    }

    fn source_version(&self) -> Option<SourceVersion> {
        None
    }

    fn single_file_edit(&self) -> Option<&SingleFileEdit> {
        None
    }

    fn read_text(&self, path: &Path) -> io::Result<Arc<SourceText>> {
        self.read_file(path)?.into_text()
    }

    fn digest_file(&self, path: &Path) -> io::Result<blake3::Hash> {
        Ok(blake3::hash(self.read_file(path)?.as_bytes()))
    }
}

/// The normal CLI reads the on-disk file system.
pub struct DiskSources;

impl SourceProvider for DiskSources {
    fn resolve(&self, path: &Path) -> io::Result<PathBuf> {
        path.canonicalize()
    }

    fn read_directory(&self, path: &Path) -> io::Result<Vec<DirectoryEntry>> {
        let mut entries = Vec::new();
        for entry in fs::read_dir(path)? {
            let entry = entry?;
            let ty = entry.file_type()?;
            let kind = if ty.is_file() {
                EntryKind::File
            } else if ty.is_dir() {
                EntryKind::Directory
            } else {
                continue;
            };
            entries.push(DirectoryEntry {
                path: entry.path(),
                kind,
            });
        }
        entries.sort_unstable_by(|left, right| left.path.cmp(&right.path));
        Ok(entries)
    }

    fn read_file(&self, path: &Path) -> io::Result<FileContents> {
        use io::Read;

        let mut bytes = Vec::new();
        open_regular_file(path)?.read_to_end(&mut bytes)?;
        Ok(match String::from_utf8(bytes) {
            Ok(text) => FileContents::Text(Arc::new(SourceText::new(text))),
            Err(error) => FileContents::Binary(error.into_bytes().into()),
        })
    }

    fn digest_file(&self, path: &Path) -> io::Result<blake3::Hash> {
        let mut file = open_regular_file(path)?;
        let mut hash = blake3::Hasher::new();
        io::copy(&mut file, &mut hash)?;
        Ok(hash.finalize())
    }
}

fn open_regular_file(path: &Path) -> io::Result<fs::File> {
    if !fs::metadata(path)?.is_file() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "expected a regular file",
        ));
    }
    fs::File::open(path)
}

/// A file that overrides the disk view for a workspace revision.
#[derive(Debug, Clone)]
pub enum FileOverlay {
    Contents(FileContents),
    Deleted,
}

/// Source input for a workspace revision, including unsaved files and deleted
/// paths. Unchanged open buffers can share their text and line index via
/// `Arc`. Obtain a fresh revision after changes to disk or the open buffers.
pub struct WorkspaceSources {
    owner: u64,
    revision: u64,
    single_file_edit: Option<SingleFileEdit>,
    files: BTreeMap<PathBuf, FileOverlay>,
    virtual_entries: BTreeMap<PathBuf, BTreeMap<PathBuf, EntryKind>>,
    paths: ReadCache<DiskPath>,
    source_reads: ReadCache<FileContents>,
    directory_reads: ReadCache<Vec<DirectoryEntry>>,
}

type ReadCache<T> = RefCell<FxHashMap<PathBuf, Result<T, Arc<io::Error>>>>;

#[derive(Clone)]
struct DiskPath {
    canonical: PathBuf,
    exists: bool,
}

impl WorkspaceSources {
    pub fn new(
        revision: u64,
        overlays: impl IntoIterator<Item = (PathBuf, FileOverlay)>,
    ) -> io::Result<Self> {
        let mut files = BTreeMap::new();
        let paths = ReadCache::default();
        for (path, contents) in overlays {
            let disk = read_once(&paths, &path, || resolve_disk_path(&path))?;
            if files.insert(disk.canonical, contents).is_some() {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    "the same file occurs more than once in the overlay",
                ));
            }
        }
        let mut virtual_entries = BTreeMap::<PathBuf, BTreeMap<PathBuf, EntryKind>>::new();
        for (file, overlay) in &files {
            if matches!(overlay, FileOverlay::Deleted) {
                continue;
            }
            let mut child = file.as_path();
            let mut kind = EntryKind::File;
            while let Some(parent) = child.parent() {
                if files.contains_key(parent) {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "an overlay file is also a directory",
                    ));
                }
                virtual_entries
                    .entry(parent.to_path_buf())
                    .or_default()
                    .insert(child.to_path_buf(), kind);
                kind = EntryKind::Directory;
                child = parent;
            }
        }
        static NEXT_OWNER: AtomicU64 = AtomicU64::new(1);
        Ok(Self {
            owner: NEXT_OWNER
                .try_update(Ordering::Relaxed, Ordering::Relaxed, |id| id.checked_add(1))
                .expect("workspace source identities exhausted"),
            revision,
            single_file_edit: None,
            files,
            virtual_entries,
            paths,
            source_reads: ReadCache::default(),
            directory_reads: ReadCache::default(),
        })
    }

    pub fn revision(&self) -> u64 {
        self.revision
    }

    /// Apply an editor text replacement after readers of the old view finish.
    /// Disk changes, file creation and deletion require a fresh source view.
    pub fn replace_open_text(
        &mut self,
        revision: u64,
        path: &Path,
        source: Arc<SourceText>,
    ) -> io::Result<()> {
        if revision <= self.revision {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "stale editor revision",
            ));
        }
        let path = self.resolve(path)?;
        let Some(FileOverlay::Contents(FileContents::Text(current))) = self.files.get_mut(&path)
        else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "file is not an open text buffer",
            ));
        };
        *current = source;
        self.single_file_edit = Some(SingleFileEdit {
            previous: SourceVersion {
                owner: self.owner,
                revision: self.revision,
            },
            path,
        });
        self.revision = revision;
        Ok(())
    }

    fn disk_path(&self, path: &Path) -> io::Result<DiskPath> {
        read_once(&self.paths, path, || resolve_disk_path(path))
    }
}

impl SourceProvider for WorkspaceSources {
    fn workspace_revision(&self) -> Option<u64> {
        Some(self.revision)
    }

    fn source_version(&self) -> Option<SourceVersion> {
        Some(SourceVersion {
            owner: self.owner,
            revision: self.revision,
        })
    }

    fn single_file_edit(&self) -> Option<&SingleFileEdit> {
        self.single_file_edit.as_ref()
    }

    fn resolve(&self, path: &Path) -> io::Result<PathBuf> {
        let DiskPath { canonical, exists } = self.disk_path(path)?;
        match self.files.get(&canonical) {
            Some(FileOverlay::Deleted) => Err(missing_file()),
            Some(FileOverlay::Contents(_)) => Ok(canonical),
            None if exists || self.virtual_entries.contains_key(&canonical) => Ok(canonical),
            None => Err(missing_file()),
        }
    }

    fn read_directory(&self, path: &Path) -> io::Result<Vec<DirectoryEntry>> {
        let canonical = self.resolve(path)?;
        read_once(&self.directory_reads, &canonical, || {
            let overlay = self.virtual_entries.get(&canonical);
            let entries = match DiskSources.read_directory(&canonical) {
                Ok(entries) => entries,
                Err(error) if error.kind() == io::ErrorKind::NotFound && overlay.is_some() => {
                    Vec::new()
                }
                Err(error) => return Err(error),
            };
            let mut combined = BTreeMap::new();
            for entry in entries {
                if !matches!(self.files.get(&entry.path), Some(FileOverlay::Deleted)) {
                    combined.insert(entry.path, entry.kind);
                }
            }
            if let Some(overlay) = overlay {
                combined.extend(overlay.iter().map(|(path, &kind)| (path.clone(), kind)));
            }
            Ok(combined
                .into_iter()
                .map(|(path, kind)| DirectoryEntry { path, kind })
                .collect())
        })
    }

    fn read_file(&self, path: &Path) -> io::Result<FileContents> {
        let canonical = self.resolve(path)?;
        if let Some(FileOverlay::Contents(contents)) = self.files.get(&canonical) {
            return Ok(contents.clone());
        }
        read_once(&self.source_reads, &canonical, || {
            DiskSources.read_file(&canonical)
        })
    }
}

fn missing_file() -> io::Error {
    io::ErrorKind::NotFound.into()
}

fn read_once<T: Clone>(
    cache: &ReadCache<T>,
    path: &Path,
    read: impl FnOnce() -> io::Result<T>,
) -> io::Result<T> {
    let mut cache = cache.borrow_mut();
    let result = cache
        .entry(path.to_path_buf())
        .or_insert_with(|| read().map_err(Arc::new));
    match result {
        Ok(result) => Ok(result.clone()),
        Err(error) => Err(io::Error::new(error.kind(), Arc::clone(error))),
    }
}

/// Resolve the existing prefix of a path. An editor can open a file
/// whose parent directory or complete path has not been saved yet.
pub fn canonical_source_path(path: &Path) -> io::Result<PathBuf> {
    resolve_disk_path(path).map(|path| path.canonical)
}

fn resolve_disk_path(path: &Path) -> io::Result<DiskPath> {
    let mut path = std::path::absolute(path)?;
    let mut suffix = Vec::<OsString>::new();
    loop {
        match path.canonicalize() {
            Ok(mut canonical) => {
                let exists = suffix.is_empty();
                let mut normalized_parent = false;
                for component in suffix.into_iter().rev() {
                    if component == ".." {
                        canonical.pop();
                        normalized_parent = true;
                    } else {
                        canonical.push(component);
                    }
                }
                if normalized_parent {
                    // A parent component may return the path to an existing
                    // directory after an unsaved directory was traversed.
                    return resolve_disk_path(&canonical);
                }
                return Ok(DiskPath { canonical, exists });
            }
            Err(error) if error.kind() == io::ErrorKind::NotFound => {
                let tail = match path.components().next_back() {
                    Some(std::path::Component::Normal(name)) => name.to_os_string(),
                    Some(std::path::Component::ParentDir) => "..".into(),
                    _ => return Err(error),
                };
                suffix.push(tail);
                assert!(path.pop());
            }
            Err(error) => return Err(error),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{
        Arc, EntryKind, FileContents, FileOverlay, Position, SourceProvider, SourceText,
        Utf16Position, WorkspaceSources,
    };
    use crate::{
        constants::MANIFEST_FILE,
        package::manifest::{Manifest, SourceSpec},
        test_support::{TempDir, with_workspace_compiler},
    };
    use std::{fs, io, rc::Rc};

    #[test]
    fn converts_scalars_bytes_and_utf16_through_crlf_and_eof() {
        let source = SourceText::new("a😀b\r\nñ\n".into());
        let after_emoji = Position { line: 0, offset: 2 };
        let utf16 = Utf16Position { line: 0, column: 3 };
        assert_eq!(source.byte_offset(after_emoji), Some(5));
        assert_eq!(source.scalar_position(5), Some(after_emoji));
        assert_eq!(source.to_utf16(after_emoji), Some(utf16));
        assert_eq!(source.from_utf16(utf16), Some(after_emoji));
        assert_eq!(
            source.from_utf16(Utf16Position { line: 0, column: 2 }),
            None
        );
        assert_eq!(source.scalar_position(7), None); // Between CR and LF.
        let end_of_line = Position { line: 0, offset: 3 };
        assert_eq!(source.byte_offset(end_of_line), Some(6));
        assert_eq!(
            source.from_utf16(Utf16Position {
                line: 0,
                column: 99
            }),
            Some(end_of_line)
        );
        let eof = Position { line: 2, offset: 0 };
        assert_eq!(source.byte_offset(eof), Some(source.text().len()));
        assert_eq!(source.scalar_position(source.text().len()), Some(eof));
        assert_eq!(
            source.to_utf16(eof),
            Some(Utf16Position { line: 2, column: 0 })
        );
    }

    fn text(source: &str) -> FileOverlay {
        FileOverlay::Contents(FileContents::Text(Arc::new(SourceText::new(source.into()))))
    }

    #[test]
    fn analysis_sees_unsaved_siblings_and_applies_file_lifecycle() {
        let root = TempDir::new("workspace-sources");
        let directory = root.join("src");
        fs::create_dir(&directory).unwrap();
        let main = directory.join("main.tr");
        let helpers = directory.join("helpers.tr");
        let nested = directory.join("string/extra.tr");
        let asset = directory.join("note.txt");
        fs::write(&main, "func call() -> int32 { 0 }").unwrap();

        let buffer = text(
            "func call() -> int32 { _ignored := \"😀\"; helper() }\r\n\
             func caption() -> string { #embed(\"note.txt\") }\n\
             func qualified() -> int32 { string::nested() }",
        );
        let build = |revision, helper| {
            Rc::new(
                WorkspaceSources::new(
                    revision,
                    [
                        (main.clone(), buffer.clone()),
                        (helpers.clone(), helper),
                        (
                            nested.clone(),
                            text("public func nested() -> int32 { 123 }"),
                        ),
                        (asset.clone(), text("visible only in the editor")),
                    ],
                )
                .unwrap(),
            )
        };
        let analyze = |sources: Rc<WorkspaceSources>| {
            with_workspace_compiler(&root, sources, None, |compiler| compiler.analyze_owned(999))
        };
        let old = build(7, text("func helper() -> int32 { 1 }"));
        assert!(old.read_directory(&directory).unwrap().iter().any(|entry| {
            entry.kind == EntryKind::Directory && entry.path.ends_with("src/string")
        }));
        assert_eq!(
            old.read_file(&asset).unwrap().as_bytes(),
            b"visible only in the editor"
        );
        let reply = analyze(old.clone());
        assert!(reply.complete, "{:?}", reply.diagnostics);
        assert_eq!(reply.revision, 7);
        let helper = reply
            .occurrences
            .iter()
            .find(|occurrence| {
                occurrence
                    .declaration
                    .as_ref()
                    .is_some_and(|declaration| declaration.name == "helper")
            })
            .expect("call resolves into the unsaved sibling");
        let source = old.read_text(&main).unwrap();
        let start = source.byte_offset(helper.source.start).unwrap();
        let end = source.byte_offset(helper.source.end).unwrap();
        assert_eq!(&source.text()[start..end], "helper");
        assert_eq!(
            source.to_utf16(helper.source.start).unwrap().column as usize,
            helper.source.start.offset + 1,
        );
        assert_eq!(helper.declaration.as_ref().unwrap().source.start.line, 0);

        let deleted = build(8, FileOverlay::Deleted);
        assert_eq!(
            deleted.read_text(&helpers).unwrap_err().kind(),
            io::ErrorKind::NotFound
        );
        let reply = analyze(deleted);
        assert!(!reply.complete);
        assert!(
            reply
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.message.contains("helper"))
        );
        assert!(old.read_text(&helpers).is_ok());

        let recreated = build(9, text("// shifted\nfunc helper() -> int32 { 2 }"));
        let reply = analyze(recreated);
        assert!(reply.complete, "{:?}", reply.diagnostics);
        let moved = reply
            .occurrences
            .iter()
            .filter_map(|occurrence| occurrence.declaration.as_ref())
            .find(|declaration| declaration.name == "helper")
            .expect("the recreated file supplies the call's definition");
        assert_eq!(moved.source.start.line, 1);

        let closed = Rc::new(WorkspaceSources::new(10, []).unwrap());
        assert_eq!(
            closed.read_text(&main).unwrap().text(),
            "func call() -> int32 { 0 }"
        );
        assert!(closed.read_text(&helpers).is_err());
        assert!(analyze(closed.clone()).complete);
        assert!(!helpers.exists());
        fs::write(&main, "func call() -> int32 { 42 }").unwrap();
        assert_eq!(
            closed.read_text(&main).unwrap().text(),
            "func call() -> int32 { 0 }"
        );
        let refreshed = WorkspaceSources::new(11, []).unwrap();
        assert_eq!(
            refreshed.read_text(&main).unwrap().text(),
            "func call() -> int32 { 42 }"
        );
    }

    #[test]
    fn manifests_resolve_new_path_dependencies_in_the_same_workspace() {
        let root = TempDir::new("workspace-manifest");
        let app = root.join("virtual-app");
        let package = app.join(MANIFEST_FILE);
        let dep = root.join("virtual-dep");
        let sources = WorkspaceSources::new(
            1,
            [
                (
                    package.clone(),
                    text(
                        "[package]\nname = 'example.org/work/app'\nkind = 'library'\n\
                         [require]\n'example.org/work/dep' = { path = '../virtual-dep' }",
                    ),
                ),
                (
                    dep.join(MANIFEST_FILE),
                    text("[package]\nname = 'example.org/work/dep'\nkind = 'library'"),
                ),
            ],
        )
        .unwrap();
        let manifest = Manifest::parse(&package, &sources).unwrap();
        let normalized = manifest.normalize(&app, &sources).unwrap();
        let SourceSpec::Path { abs } = &normalized.dependencies["dep"].source else {
            panic!("expected an unsaved path dependency");
        };
        assert_eq!(abs, &root.canonicalize().unwrap().join("virtual-dep"));
        let dep_manifest = Manifest::parse(&abs.join(MANIFEST_FILE), &sources).unwrap();
        assert_eq!(dep_manifest.package.name.as_str(), "example.org/work/dep");
    }

    #[test]
    fn frozen_dependencies_recheck_assets_against_the_revision() {
        let root = TempDir::new("workspace-asset");
        let source = root.join("src/lib.tr");
        let asset = root.join("src/data.bin");
        let build = |revision, bytes: [u8; 3]| {
            Rc::new(
                WorkspaceSources::new(
                    revision,
                    [
                        (
                            source.clone(),
                            text("public const DATA: [uint8; 3] = #embedBytes(\"data.bin\")"),
                        ),
                        (
                            asset.clone(),
                            FileOverlay::Contents(FileContents::Binary(Arc::from(bytes))),
                        ),
                    ],
                )
                .unwrap(),
            )
        };
        let original = build(1, [0, 255, 1]);
        let frozen = with_workspace_compiler(&root, original.clone(), None, |compiler| {
            compiler.freeze_dependency().unwrap_or_else(|error| {
                panic!(
                    "{error}: {:?}",
                    compiler.context.dcx().take_recorded_diagnostics()
                )
            })
        });
        with_workspace_compiler(&root, original, None, |compiler| {
            frozen.hydrate(compiler.context).unwrap()
        });
        let changed = build(2, [0, 255, 2]);
        with_workspace_compiler(&root, changed, None, |compiler| {
            assert_eq!(
                frozen.hydrate(compiler.context).unwrap_err().to_string(),
                "embedded asset 'src/data.bin' changed"
            );
            assert!(
                compiler
                    .context
                    .try_resolution_output(compiler.context.package_index())
                    .is_none()
            );
        });
    }
}
