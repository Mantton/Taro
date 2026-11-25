//! A disposable analysis worker exercised without LLVM or process recycling.
#![cfg(not(feature = "llvm"))]

use std::{
    alloc::{GlobalAlloc, Layout, System},
    fs,
    panic::{AssertUnwindSafe, catch_unwind, resume_unwind},
    path::{Path, PathBuf},
    rc::Rc,
    sync::atomic::{AtomicUsize, Ordering::Relaxed},
};

use compiler::{
    PackageIndex,
    compile::{
        Compiler,
        analysis_products::AnalysisProduct,
        config::{Config, PackageKind, StdMode},
        context::{CompilerArenas, CompilerContext, CompilerStore, Gcx},
        frozen_dependencies::FrozenDependency,
        target_facts::TargetFacts,
    },
    diagnostics::DiagCtx,
};

#[path = "../../test_support.rs"]
mod files;

/// Count requested Rust heap storage, including the capacity of arena chunks
/// and hash tables. This binary has one test and runs its analyses serially.
struct AccountingAllocator;

static LIVE_BYTES: AtomicUsize = AtomicUsize::new(0);
static LIVE_BLOCKS: AtomicUsize = AtomicUsize::new(0);
static PEAK_BYTES: AtomicUsize = AtomicUsize::new(0);

// SAFETY: The allocator forwards the original pointers and layouts to System.
// Its counters are atomic and their updates cannot allocate.
unsafe impl GlobalAlloc for AccountingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let pointer = unsafe { System.alloc(layout) };
        if !pointer.is_null() {
            let previous = LIVE_BYTES.fetch_add(layout.size(), Relaxed);
            LIVE_BLOCKS.fetch_add(1, Relaxed);
            PEAK_BYTES.fetch_max(previous + layout.size(), Relaxed);
        }
        pointer
    }

    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        LIVE_BLOCKS.fetch_sub(1, Relaxed);
        LIVE_BYTES.fetch_sub(layout.size(), Relaxed);
        unsafe { System.dealloc(pointer, layout) };
    }
}

#[global_allocator]
static ALLOCATOR: AccountingAllocator = AccountingAllocator;

fn live_heap() -> (usize, usize) {
    (LIVE_BYTES.load(Relaxed), LIVE_BLOCKS.load(Relaxed))
}

fn config(root: PathBuf, id: &str, index: usize) -> Config {
    Config {
        name: id.into(),
        identifier: id.into(),
        src: root,
        dependencies: Default::default(),
        index: PackageIndex::new(index),
        kind: PackageKind::Library,
        executable_out: None,
        no_std_prelude: true,
        is_script: false,
        profile: Default::default(),
        codegen: Default::default(),
        overflow_checks: false,
        debug: Default::default(),
        harness_mode: Default::default(),
        std_mode: StdMode::BootstrapStd,
        is_std_provider: false,
        lint_warnings: false,
    }
}

fn write_source(config: &Config, text: &str) {
    let directory = config.src.join("src");
    fs::create_dir_all(&directory).unwrap();
    fs::write(directory.join("lib.tr"), text).unwrap();
}

struct Worker {
    root: PathBuf,
    target: TargetFacts,
    dependency: Config,
    active: Config,
}

impl Worker {
    fn new(root: &Path) -> Self {
        let dependency = config(root.join("dep"), "test/dep", 1);
        let mut active = config(root.join("app"), "test/app", 2);
        active.dependencies.insert("dep".into(), "test/dep".into());
        write_source(&dependency, "public const func width() -> usize { 2 }");
        let target =
            toml::from_str("triple = 'x86_64-unknown-linux-gnu'\npointer_bits = 64").unwrap();
        Self {
            root: root.to_path_buf(),
            target,
            dependency,
            active,
        }
    }

    fn with_scratch<R>(
        &self,
        run: impl for<'scratch> FnOnce(&'scratch CompilerContext<'scratch>) -> R,
    ) -> R {
        let diagnostics = Rc::new(DiagCtx::new(self.root.clone()));
        diagnostics.enable_recording();
        let arenas = CompilerArenas::new();
        let store =
            CompilerStore::new_for_analysis(&arenas, self.root.join("target"), self.target.clone());
        let scratch = CompilerContext::new(diagnostics, store);
        run(&scratch)
    }

    fn freeze(&self) -> FrozenDependency {
        self.with_scratch(|scratch| {
            let config = scratch.store.arenas.configs.alloc(self.dependency.clone());
            let mut compiler = Compiler::new(scratch, config);
            compiler.freeze_dependency().unwrap()
        })
    }

    fn analyze(&self, snapshot: &FrozenDependency, revision: u64, cancel: bool) -> AnalysisProduct {
        self.with_scratch(|scratch| {
            let arenas = scratch.store.arenas;
            let config = arenas.configs.alloc(self.dependency.clone());
            snapshot.hydrate(Gcx::new(scratch, config)).unwrap();
            let active = arenas.configs.alloc(self.active.clone());
            let mut compiler = Compiler::new(scratch, active);
            let answer = compiler.analyze_owned(revision);
            if cancel {
                // Model cancellation after analysis allocated data and before
                // a reply escapes. Resume unwinding without a panic-hook log.
                resume_unwind(Box::new(Cancelled));
            }
            answer
        })
    }
}

#[derive(Debug)]
struct Cancelled;

#[test]
fn frozen_and_scratch_allocations_have_independent_lifetimes() {
    let root = files::TempDir::new("disposable-analysis");
    let worker = Worker::new(&root);
    let edits = std::env::var("TARO_LSP_SOAK_EDITS")
        .map(|count| {
            count
                .parse::<u32>()
                .expect("TARO_LSP_SOAK_EDITS is an unsigned edit count")
        })
        .unwrap_or(16);
    let asset = worker.active.src.join("payload.bin");
    let sibling = worker.active.src.join("src/transient.tr");
    let source = "import dep::width\n\
                  const captions: [[string; 2]; 1] = [[\"first\", \"second\"]]\n\
                  const bytes: [uint8; 4] = #embedBytes(\"../payload.bin\")\n\
                  func buffer() -> [int32; width()] { [1, 2] }\n\
                  func useWidth() -> usize { width() }\n\
                  func selected(_ flag: bool) -> bool { flag }\n\
                  func selected(_ value: int32) -> int32 { value }\n\
                  func local() -> int32 { firstName := 42; selected(firstName) }";
    let cancelled = |snapshot: &FrozenDependency| {
        let result = catch_unwind(AssertUnwindSafe(|| worker.analyze(snapshot, 0, true)));
        assert!(result.unwrap_err().is::<Cancelled>());
    };
    // Warm process initialization and the unwind runtime before measuring.
    write_source(&worker.active, source);
    fs::write(&asset, 0u32.to_le_bytes()).unwrap();
    {
        let snapshot = worker.freeze();
        assert!(worker.analyze(&snapshot, 0, false).complete);
        cancelled(&snapshot);
    }

    let empty = live_heap();
    let snapshot = worker.freeze();
    let frozen = live_heap();
    assert_eq!(frozen, (empty.0 + snapshot.retained_bytes(), empty.1 + 1));
    PEAK_BYTES.store(frozen.0, Relaxed);

    let delayed = worker.analyze(&snapshot, 1, false);
    assert!(delayed.complete, "{:?}", delayed.diagnostics);
    let holding_reply = live_heap();
    for edit in 1..=edits {
        let revision = u64::from(edit) + 1;
        let edited = if edit % 500 == 0 {
            source.to_owned()
        } else {
            source
                .replace("\"first\"", &format!("\"revision {revision}\""))
                .replace("firstName", &format!("name{revision}"))
                .replace("_ flag: bool", &format!("tag{revision} flag: bool"))
        };
        write_source(&worker.active, &edited);
        fs::write(
            &asset,
            (if edit % 500 == 0 { 0 } else { edit }).to_le_bytes(),
        )
        .unwrap();
        if edit % 3 == 1 {
            fs::write(
                &sibling,
                format!("func transient{revision}() -> int32 {{ 1 }}"),
            )
            .unwrap();
        }
        let answer = worker.analyze(&snapshot, revision, false);
        assert!(answer.complete, "{:?}", answer.diagnostics);
        drop(answer);
        drop(edited);
        if edit % 3 == 1 {
            fs::remove_file(&sibling).unwrap();
        }
        assert_eq!(live_heap(), holding_reply, "after revision {revision}");
    }
    cancelled(&snapshot);
    assert_eq!(live_heap(), holding_reply, "after cancellation");

    write_source(&worker.active, "func broken() { undefinedName() }");
    let failed = worker.analyze(&snapshot, u64::from(edits) + 2, false);
    assert!(!failed.complete);
    assert!(!failed.diagnostics.is_empty());
    drop(failed);
    assert_eq!(live_heap(), holding_reply, "after a reported error");

    assert_eq!(delayed.revision, 1);
    assert!(delayed.occurrences.iter().any(|occurrence| {
        occurrence
            .declaration
            .as_ref()
            .is_some_and(|definition| definition.name == "width")
    }));
    drop(delayed);
    assert_eq!(
        live_heap(),
        frozen,
        "after the delayed reader releases its reply"
    );
    let peak_scratch_bytes = PEAK_BYTES.load(Relaxed) - frozen.0;

    drop(snapshot);
    assert_eq!(live_heap(), empty, "after dropping the frozen dependency");
    println!(
        "Replayed {edits} edits. Frozen payload: {} requested bytes. Peak heap above frozen baseline: {peak_scratch_bytes} bytes.",
        frozen.0 - empty.0
    );
}
