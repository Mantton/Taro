use crate::{
    codegen::{
        abi,
        artifact::ModuleArtifact,
        gc_stack_maps::{PendingLogicalFrame, StackMapSiteKind, strip_object},
        mangle::{mangle, mangle_instance},
    },
    compile::{
        config::{
            BuildProfile, DebugInfo, LtoMode, ModuleArtifactKind, OptLevel, OptimizationMode,
        },
        context::{Gcx, GlobalContext},
    },
    error::CompileResult,
    hir,
    mir::{self, Operand, Place},
    sema::{
        models::{
            ConstKind, ConstValue, FloatTy, GenericArguments, IntTy, InterfaceReference,
            StructRepr, Ty, TyKind, UIntTy,
        },
        resolve::models::DefinitionKind,
        tycheck::utils::instantiate::instantiate_ty_with_args,
    },
    span::Symbol,
    specialize::{Instance, InstanceKind, resolve_instance},
};
use inkwell::{
    AddressSpace, FloatPredicate, IntPredicate,
    attributes::{Attribute, AttributeLoc},
    basic_block::BasicBlock,
    builder::Builder,
    context::Context,
    intrinsics::Intrinsic,
    module::{Linkage, Module},
    passes::PassBuilderOptions,
    targets::{FileType, TargetData, TargetMachine},
    types::{
        BasicMetadataTypeEnum, BasicType, BasicTypeEnum, FloatType, FunctionType, IntType,
        StructType,
    },
    values::{
        AggregateValue, BasicMetadataValueEnum, BasicValue, BasicValueEnum, CallSiteValue,
        FunctionValue, IntValue, PointerValue,
    },
};
use rustc_hash::{FxHashMap, FxHashSet};
use std::{
    fs,
    time::{Duration, Instant},
};

mod atomics;
mod c_extensions;
mod c_strings;
mod classes;
mod coverage;
mod debug;
mod erased_openings;
mod existentials;
mod gc_classes;
mod gc_layout;
pub(crate) mod gc_root_stores;
mod gc_sites;
#[cfg(all(test, unix))]
mod gc_source_tests;
mod gc_strings;
mod gc_values;
mod intrinsics;

mod strings;

#[cfg(test)]
mod integer_arith_tests;
#[cfg(test)]
mod repeat_tests;
#[cfg(test)]
mod shared_access_tests;
#[cfg(test)]
mod test_support;

mod normalize;
mod references;
mod statics;
mod task_output;
mod witness;

#[derive(Clone, Copy)]
enum CallTarget<'llvm> {
    Direct(FunctionValue<'llvm>),
    Indirect(FunctionType<'llvm>, PointerValue<'llvm>),
}

const NON_AARCH64_INDIRECT_RETURN_THRESHOLD_BYTES: u64 = 256;
const AARCH64_INDIRECT_RETURN_THRESHOLD_BYTES: u64 = 24;
const NON_AARCH64_INDIRECT_ARG_THRESHOLD_BYTES: u64 = 2048;
const AARCH64_INDIRECT_ARG_THRESHOLD_BYTES: u64 = 24;
const LARGE_AGGREGATE_MOVE_MEMMOVE_THRESHOLD_BYTES: u64 = 1024;
const ENV_ARGC_GLOBAL_NAME: &str = "__taro_env_argc";
const ENV_ARGV_GLOBAL_NAME: &str = "__taro_env_argv";

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LlvmOptimizationPipeline {
    Function(&'static str),
    Module(&'static str),
}

fn place_operand<'a, 'ctx>(op: &'a Operand<'ctx>) -> Option<&'a Place<'ctx>> {
    match op {
        Operand::Copy(place) | Operand::CopyWith(place, _) => Some(place),
        Operand::Constant(_) => None,
    }
}

fn llvm_optimization_pipeline(
    profile: BuildProfile,
    optimization: OptimizationMode,
    lto: LtoMode,
) -> LlvmOptimizationPipeline {
    match (lto, optimization) {
        // LLVM's pre-link and post-link LTO pipelines are designed as a pair.
        // Keep mem2reg at O0 because Taro's MIR lowering intentionally begins
        // every local in stack form.
        (LtoMode::Full, OptimizationMode::Level(OptLevel::O0)) => {
            LlvmOptimizationPipeline::Module("function(mem2reg),lto-pre-link<O0>")
        }
        (LtoMode::Full, OptimizationMode::Level(OptLevel::O1)) => {
            LlvmOptimizationPipeline::Module("lto-pre-link<O1>")
        }
        (LtoMode::Full, OptimizationMode::Level(OptLevel::O2)) => {
            LlvmOptimizationPipeline::Module("lto-pre-link<O2>")
        }
        (LtoMode::Full, OptimizationMode::Level(OptLevel::O3)) => {
            LlvmOptimizationPipeline::Module("lto-pre-link<O3>")
        }
        (LtoMode::Full, OptimizationMode::Level(OptLevel::Os)) => {
            LlvmOptimizationPipeline::Module("lto-pre-link<Os>")
        }
        (LtoMode::Full, OptimizationMode::Level(OptLevel::Oz)) => {
            LlvmOptimizationPipeline::Module("lto-pre-link<Oz>")
        }
        // ThinLTO keeps modules separate. Its pre-link pipeline prepares each
        // package for summary analysis and later cross-module importing.
        (LtoMode::Thin, OptimizationMode::Baseline) => match profile {
            BuildProfile::Debug => {
                LlvmOptimizationPipeline::Module("function(mem2reg),thinlto-pre-link<O0>")
            }
            BuildProfile::Release => LlvmOptimizationPipeline::Module("thinlto-pre-link<O2>"),
        },
        (LtoMode::Thin, OptimizationMode::Level(OptLevel::O0)) => {
            LlvmOptimizationPipeline::Module("function(mem2reg),thinlto-pre-link<O0>")
        }
        (LtoMode::Thin, OptimizationMode::Level(OptLevel::O1)) => {
            LlvmOptimizationPipeline::Module("thinlto-pre-link<O1>")
        }
        (LtoMode::Thin, OptimizationMode::Level(OptLevel::O2)) => {
            LlvmOptimizationPipeline::Module("thinlto-pre-link<O2>")
        }
        (LtoMode::Thin, OptimizationMode::Level(OptLevel::O3)) => {
            LlvmOptimizationPipeline::Module("thinlto-pre-link<O3>")
        }
        (LtoMode::Thin, OptimizationMode::Level(OptLevel::Os)) => {
            LlvmOptimizationPipeline::Module("thinlto-pre-link<Os>")
        }
        (LtoMode::Thin, OptimizationMode::Level(OptLevel::Oz)) => {
            LlvmOptimizationPipeline::Module("thinlto-pre-link<Oz>")
        }
        // Keep the certified pre-rollout pipelines available as a comparison
        // baseline until Story 4 promotes release builds to LLVM O2.
        (_, OptimizationMode::Baseline) => match profile {
            BuildProfile::Debug => LlvmOptimizationPipeline::Function("mem2reg"),
            BuildProfile::Release => LlvmOptimizationPipeline::Function(
                "mem2reg,instcombine,reassociate,gvn,simplifycfg",
            ),
        },
        // Every MIR local begins as an alloca. Even at O0, retain mem2reg so
        // explicit `-O0` has the same usable baseline IR shape as debug builds.
        (LtoMode::Off, OptimizationMode::Level(OptLevel::O0)) => {
            LlvmOptimizationPipeline::Function("mem2reg")
        }
        (LtoMode::Off, OptimizationMode::Level(OptLevel::O1)) => {
            LlvmOptimizationPipeline::Module("default<O1>")
        }
        (LtoMode::Off, OptimizationMode::Level(OptLevel::O2)) => {
            LlvmOptimizationPipeline::Module("default<O2>")
        }
        (LtoMode::Off, OptimizationMode::Level(OptLevel::O3)) => {
            LlvmOptimizationPipeline::Module("default<O3>")
        }
        (LtoMode::Off, OptimizationMode::Level(OptLevel::Os)) => {
            LlvmOptimizationPipeline::Module("default<Os>")
        }
        (LtoMode::Off, OptimizationMode::Level(OptLevel::Oz)) => {
            LlvmOptimizationPipeline::Module("default<Oz>")
        }
    }
}

fn has_llvm_function_body(function: FunctionValue<'_>) -> bool {
    function.count_basic_blocks() != 0
}

fn llvm_inline_attribute_name(
    attributes: impl IntoIterator<Item = hir::KnownAttribute>,
) -> Option<&'static str> {
    attributes
        .into_iter()
        .find_map(|attribute| match attribute {
            // `@inline` is documented as a hint. MIR already attempts eager
            // inlining; InlineHint lets LLVM make the final profitability decision
            // when the call could not be inlined at MIR level.
            hir::KnownAttribute::Inline => Some("inlinehint"),
            // Unlike a hint, `@noinline` is a language contract and must survive
            // into LLVM's optimizer.
            hir::KnownAttribute::NoInline => Some("noinline"),
            _ => None,
        })
}

fn add_llvm_enum_function_attribute(
    context: &Context,
    function: FunctionValue<'_>,
    attribute_name: &str,
) {
    let kind_id = Attribute::get_named_enum_kind_id(attribute_name);
    debug_assert_ne!(kind_id, 0, "LLVM must recognize `{attribute_name}`");
    function.add_attribute(
        AttributeLoc::Function,
        context.create_enum_attribute(kind_id, 0),
    );
}

fn add_llvm_enum_function_attribute_with_value(
    context: &Context,
    function: FunctionValue<'_>,
    attribute_name: &str,
    value: u64,
) {
    let kind_id = Attribute::get_named_enum_kind_id(attribute_name);
    debug_assert_ne!(kind_id, 0, "LLVM must recognize `{attribute_name}`");
    function.add_attribute(
        AttributeLoc::Function,
        context.create_enum_attribute(kind_id, value),
    );
}

fn add_llvm_string_function_attribute(
    context: &Context,
    function: FunctionValue<'_>,
    key: &str,
    value: &str,
) {
    function.add_attribute(
        AttributeLoc::Function,
        context.create_string_attribute(key, value),
    );
}

fn target_is_aarch64(triple: &str) -> bool {
    matches!(
        triple.split('-').next(),
        Some("aarch64" | "arm64" | "arm64e")
    )
}

fn indirect_return_threshold_for_triple(triple: &str) -> u64 {
    if target_is_aarch64(triple) {
        AARCH64_INDIRECT_RETURN_THRESHOLD_BYTES
    } else {
        NON_AARCH64_INDIRECT_RETURN_THRESHOLD_BYTES
    }
}

fn indirect_arg_threshold_for_triple(triple: &str) -> u64 {
    if target_is_aarch64(triple) {
        AARCH64_INDIRECT_ARG_THRESHOLD_BYTES
    } else {
        NON_AARCH64_INDIRECT_ARG_THRESHOLD_BYTES
    }
}

fn llvm_type_contains_array(ty: BasicTypeEnum<'_>) -> bool {
    match ty {
        BasicTypeEnum::ArrayType(_) => true,
        BasicTypeEnum::StructType(struct_ty) => struct_ty
            .get_field_types()
            .into_iter()
            .any(llvm_type_contains_array),
        _ => false,
    }
}

fn write_llvm_bitcode(module: &Module<'_>, path: &std::path::Path) -> std::io::Result<()> {
    let buffer = module.write_bitcode_to_memory();
    let bytes = buffer.as_slice();
    let bytes = bytes.strip_suffix(&[0]).unwrap_or(bytes);
    if !has_llvm_bitcode_magic(bytes) {
        return Err(std::io::Error::other(
            "LLVM produced a buffer without bitcode magic",
        ));
    }
    fs::write(path, bytes)
}

fn has_llvm_bitcode_magic(bytes: &[u8]) -> bool {
    // LLVM emits either raw bitcode or the target-independent bitcode wrapper
    // used by Apple toolchains. Both forms are accepted by LLVM's parser.
    bytes.starts_with(b"BC\xc0\xde") || bytes.starts_with(b"\xde\xc0\x17\x0b")
}

#[derive(Debug, Clone, Copy, Default)]
pub struct CodegenPhaseTimings {
    pub module_setup: Duration,
    pub declare_instances: Duration,
    pub lower_instances: Duration,
    pub emit_entry_or_harness: Duration,
    pub verify: Duration,
    pub optimize_ir: Duration,
    pub emit_artifact: Duration,
}

pub(crate) enum PackageEntry {
    Main,
    Tests(Vec<crate::compile::test_collector::TestCase>),
    Benchmarks(Vec<crate::compile::bench_collector::BenchmarkCase>),
    Fuzz(crate::compile::fuzz_collector::FuzzTarget),
}

/// Lower MIR and its selected entry point into one LLVM module.
pub(crate) fn emit_package_with_timings<'gcx>(
    package: &'gcx mir::MirPackage<'gcx>,
    gcx: GlobalContext<'gcx>,
    entry: PackageEntry,
) -> CompileResult<(ModuleArtifact, CodegenPhaseTimings)> {
    let mut timings = CodegenPhaseTimings::default();

    let phase_started_at = Instant::now();
    let context = Context::create();
    let module = context.create_module(&gcx.config.identifier);
    let builder = context.create_builder();

    // Use the shared target layout from CompilerStore.
    let target_layout = &gcx.store.target_layout;
    module.set_data_layout(&target_layout.data_layout());
    module.set_triple(&target_layout.triple());
    timings.module_setup = phase_started_at.elapsed();

    let mut emitter = Emitter::new(&context, module, builder, gcx)?;
    let errors_at_start = gcx.dcx().error_count();
    let phase_started_at = Instant::now();
    emitter.declare_instances();
    timings.declare_instances = phase_started_at.elapsed();

    let phase_started_at = Instant::now();
    emitter.lower_instances()?;
    timings.lower_instances = phase_started_at.elapsed();

    emitter.emit_dispatch_registration_ctor();

    let phase_started_at = Instant::now();
    match entry {
        PackageEntry::Main => emitter.emit_start_shim(package),
        PackageEntry::Tests(tests) => emitter.emit_test_harness(&tests),
        PackageEntry::Benchmarks(benchmarks) => emitter.emit_bench_harness(&benchmarks),
        PackageEntry::Fuzz(target) => emitter.emit_fuzz_harness(&target),
    }
    timings.emit_entry_or_harness = phase_started_at.elapsed();
    // Some lowering helpers report internal errors without unwinding, such
    // as witness tables built on demand. Never emit an object after them.
    if gcx.dcx().error_count() > errors_at_start {
        return Err(crate::error::ReportedError);
    }

    emitter.finalize_debug_info();
    emitter.finalize_coverage()?;
    c_extensions::finalize(&emitter)?;

    let phase_started_at = Instant::now();
    if let Err(e) = emitter.module.verify() {
        let msg = format!("invalid LLVM module: {}", e.to_string());
        gcx.dcx().emit_error(msg, None);
        return Err(crate::error::ReportedError);
    }
    timings.verify = phase_started_at.elapsed();

    let phase_started_at = Instant::now();
    dump_matching_functions(&emitter.module, "before optimization");
    emitter.run_optimization_passes()?;
    gc_root_stores::elide_redundant_root_stores(&emitter.module);
    dump_matching_functions(&emitter.module, "after optimization");
    timings.optimize_ir = phase_started_at.elapsed();

    let phase_started_at = Instant::now();
    if let Err(e) = emitter.module.verify() {
        let msg = format!("LLVM passes produced an invalid module: {}", e.to_string());
        gcx.dcx().emit_error(msg, None);
        return Err(crate::error::ReportedError);
    }
    timings.verify += phase_started_at.elapsed();

    // Dump LLVM IR if requested
    if gcx.config.debug.dump_llvm {
        eprintln!("\n=== LLVM IR for {} ===", gcx.config.name);
        let ir = emitter.module.print_to_string().to_string();
        eprintln!("{ir}");
        eprintln!("=== End LLVM Dump ===\n");
    }

    let phase_started_at = Instant::now();
    let artifact = emitter.emit_module_artifact()?;
    timings.emit_artifact = phase_started_at.elapsed();

    gcx.cache_module_artifact(artifact.clone());
    Ok((artifact, timings))
}

/// Debugging aid: `TARO_DEBUG_DUMP_FN=<substring>` prints matching LLVM
/// functions around the optimizer.
fn dump_matching_functions(module: &Module<'_>, stage: &str) {
    let Ok(filter) = std::env::var("TARO_DEBUG_DUMP_FN") else {
        return;
    };
    for function in module.get_functions() {
        if function.get_name().to_string_lossy().contains(&filter) {
            eprintln!(
                "; {stage}\n{}",
                inkwell::values::AnyValue::print_to_string(&function).to_string()
            );
        }
    }
}

struct Emitter<'llvm, 'gcx> {
    context: &'llvm Context,
    module: Module<'llvm>,
    builder: Builder<'llvm>,
    debug: Option<debug::DebugContext<'llvm>>,
    coverage: Option<coverage::CoverageContext>,
    gcx: GlobalContext<'gcx>,
    functions: FxHashMap<Instance<'gcx>, (FunctionValue<'llvm>, abi::FnAbi<'gcx>)>,
    globals: FxHashMap<hir::DefinitionID, PointerValue<'llvm>>,
    strings: FxHashMap<Symbol, PointerValue<'llvm>>,
    target_machine: TargetMachine,
    target_data: inkwell::targets::TargetData,
    gc_descriptors: FxHashMap<Ty<'gcx>, PointerValue<'llvm>>,
    /// Local statics holding managed pointers, with their exact descriptors.
    static_gc_roots: Vec<(PointerValue<'llvm>, PointerValue<'llvm>)>,
    gc_value_descriptors: FxHashMap<Ty<'gcx>, PointerValue<'llvm>>,
    enum_layouts: FxHashMap<
        (
            hir::DefinitionID,
            GenericArguments<'gcx>,
            GenericArguments<'gcx>,
        ),
        EnumLayout<'llvm>,
    >,
    witness_tables: FxHashMap<(Ty<'gcx>, InterfaceReference<'gcx>), PointerValue<'llvm>>,
    interface_descriptors: FxHashMap<InterfaceReference<'gcx>, PointerValue<'llvm>>,
    type_metadata: FxHashMap<Ty<'gcx>, PointerValue<'llvm>>,
    /// Cache for witness table thunks: (type_head, interface, impl_method_id) -> thunk_fn_ptr
    witness_thunks:
        FxHashMap<(Ty<'gcx>, InterfaceReference<'gcx>, hir::DefinitionID), PointerValue<'llvm>>,
    rt_conformance_entry_ty: inkwell::types::StructType<'llvm>,
    rt_type_metadata_ty: inkwell::types::StructType<'llvm>,
    usize_ty: inkwell::types::IntType<'llvm>,
    // Internal candidate backend, exercised through source/object tests. This
    // becomes unconditional at G26; it is not a public language option.
    pending_gc_stack_maps: Vec<crate::codegen::gc_stack_maps::PendingStackMapRecord>,
    #[cfg(test)]
    gc_metadata_test_hook: Option<fn(&mut crate::codegen::gc_pc_metadata::PcMetadata)>,
    current_gc_frame: Option<gc_sites::GcStackMapFrame<'llvm, 'gcx>>,
    current_stack_map_ordinal: u64,
    current_stack_map_selector: Option<PointerValue<'llvm>>,
    current_body: Option<&'gcx mir::Body<'gcx>>,
    current_mir_location: Option<mir::analysis::liveness::MirLocation>,
    eh_personality: Option<FunctionValue<'llvm>>,
    eh_slot: Option<PointerValue<'llvm>>,
    /// Set while lowering a foreign call's arguments: function values passed
    /// there become callback entry shims.
    lowering_foreign_args: bool,
    current_fn: Option<FunctionValue<'llvm>>,
    current_fn_abi: Option<abi::FnAbi<'gcx>>,
    current_sret_ptr: Option<PointerValue<'llvm>>,
    current_source_scope: mir::SourceScopeId,
    current_span: Option<crate::span::Span>,
    indirect_return_threshold_bytes: u64,
    indirect_arg_threshold_bytes: u64,
    repeat_memset_enabled: bool,
    repeat_memset_min_bytes: u64,
    /// Current substitution context for monomorphization
    current_subst: GenericArguments<'gcx>,
    env_argc_storage: Option<PointerValue<'llvm>>,
    env_argv_storage: Option<PointerValue<'llvm>>,
    pending_function_instances: Vec<Instance<'gcx>>,
    class_descriptors: FxHashMap<Ty<'gcx>, PointerValue<'llvm>>,
    class_registrations: FxHashMap<
        (Ty<'gcx>, Instance<'gcx>),
        (hir::DefinitionID, GenericArguments<'gcx>, Instance<'gcx>),
    >,
    erased_opening_registrations:
        FxHashMap<(Ty<'gcx>, Instance<'gcx>), Option<PointerValue<'llvm>>>,
}

#[derive(Clone, Copy)]
enum LocalStorage<'llvm> {
    Value(Option<BasicValueEnum<'llvm>>),
    Stack(PointerValue<'llvm>),
}

#[derive(Clone, Copy)]
enum StdPanicCallKind {
    Panic,
    Todo,
    Unreachable,
}

impl<'llvm, 'gcx> Emitter<'llvm, 'gcx> {
    fn new(
        context: &'llvm Context,
        module: Module<'llvm>,
        builder: Builder<'llvm>,
        gcx: GlobalContext<'gcx>,
    ) -> CompileResult<Self> {
        let target_machine = gcx.store.target_layout.create_target_machine(
            gcx.dcx(),
            gcx.config.profile,
            gcx.config.codegen.optimization,
        )?;
        let target_data = target_machine.get_target_data();
        let target_triple = gcx.store.target_layout.triple();
        let target_triple_str = target_triple.as_str().to_str().unwrap_or("");
        let default_indirect_return_threshold =
            indirect_return_threshold_for_triple(target_triple_str);
        let indirect_return_threshold_bytes = default_indirect_return_threshold;
        let indirect_arg_threshold_bytes = indirect_arg_threshold_for_triple(target_triple_str);
        let usize_ty = context.ptr_sized_int_type(&target_data, None);
        let opaque_ptr = context.ptr_type(AddressSpace::default());
        let rt_conformance_entry_ty =
            context.struct_type(&[opaque_ptr.into(), opaque_ptr.into()], false);
        let rt_type_metadata_ty = context.struct_type(
            &[opaque_ptr.into(), usize_ty.into(), opaque_ptr.into()],
            false,
        );
        let repeat_memset_enabled = std::env::var("TARO_EXPERIMENTAL_REPEAT_MEMSET")
            .ok()
            .map(|v| {
                let v = v.trim();
                !v.is_empty() && v != "0" && !v.eq_ignore_ascii_case("false")
            })
            .unwrap_or(false);
        let repeat_memset_min_bytes = std::env::var("TARO_EXPERIMENTAL_REPEAT_MEMSET_MIN_BYTES")
            .ok()
            .and_then(|v| v.trim().parse::<u64>().ok())
            .unwrap_or(0);
        let debug = matches!(gcx.config.debug.debug_info, DebugInfo::LineTables)
            .then(|| debug::DebugContext::new(context, &module, gcx));
        let coverage = gcx
            .config
            .codegen
            .coverage
            .then(coverage::CoverageContext::new);
        Ok(Emitter {
            context,
            module,
            builder,
            debug,
            coverage,
            gcx,
            functions: FxHashMap::default(),
            globals: FxHashMap::default(),
            strings: FxHashMap::default(),
            target_machine,
            target_data,
            gc_descriptors: FxHashMap::default(),
            static_gc_roots: Vec::new(),
            gc_value_descriptors: FxHashMap::default(),
            enum_layouts: FxHashMap::default(),
            witness_tables: FxHashMap::default(),
            interface_descriptors: FxHashMap::default(),
            type_metadata: FxHashMap::default(),
            witness_thunks: FxHashMap::default(),
            rt_conformance_entry_ty,
            rt_type_metadata_ty,
            usize_ty,
            pending_gc_stack_maps: Vec::new(),
            #[cfg(test)]
            gc_metadata_test_hook: None,
            current_gc_frame: None,
            current_stack_map_ordinal: 0,
            current_stack_map_selector: None,
            current_body: None,
            current_mir_location: None,
            eh_personality: None,
            eh_slot: None,
            lowering_foreign_args: false,
            current_fn: None,
            current_fn_abi: None,
            current_sret_ptr: None,
            current_source_scope: mir::SourceScopeId::from_raw(0),
            current_span: None,
            indirect_return_threshold_bytes,
            indirect_arg_threshold_bytes,
            repeat_memset_enabled,
            repeat_memset_min_bytes,
            current_subst: GenericArguments::empty(),
            env_argc_storage: None,
            env_argv_storage: None,
            pending_function_instances: Vec::new(),
            class_descriptors: FxHashMap::default(),
            class_registrations: FxHashMap::default(),
            erased_opening_registrations: FxHashMap::default(),
        })
    }

    fn enum_layout_for(
        &mut self,
        def_id: hir::DefinitionID,
        adt_args: GenericArguments<'gcx>,
    ) -> EnumLayout<'llvm> {
        let subst = self.current_subst;
        let key = (def_id, adt_args, subst);
        if let Some(&layout) = self.enum_layouts.get(&key) {
            return layout;
        }

        let layout = enum_layout(
            self.context,
            self.gcx,
            &self.target_data,
            def_id,
            adt_args,
            subst,
        );
        self.enum_layouts.insert(key, layout);
        layout
    }

    fn insert_function_instance(
        &mut self,
        instance: Instance<'gcx>,
        function: FunctionValue<'llvm>,
        fn_abi: abi::FnAbi<'gcx>,
    ) {
        self.apply_source_function_attributes(instance, function);
        assert!(
            self.functions
                .insert(instance, (function, fn_abi))
                .is_none()
        );
        self.pending_function_instances.push(instance);
    }

    fn apply_source_function_attributes(
        &self,
        instance: Instance<'gcx>,
        function: FunctionValue<'llvm>,
    ) {
        let InstanceKind::Item(def_id) = instance.kind() else {
            return;
        };
        let Some(attribute_name) = llvm_inline_attribute_name(
            self.gcx
                .attributes_of(def_id)
                .iter()
                .filter_map(|attribute| attribute.as_known(self.gcx)),
        ) else {
            return;
        };

        add_llvm_enum_function_attribute(self.context, function, attribute_name);
    }

    fn instance_for_call(
        &self,
        def_id: hir::DefinitionID,
        args: GenericArguments<'gcx>,
    ) -> Instance<'gcx> {
        let args = self.resolve_generic_args(args);
        resolve_instance(self.gcx, def_id, args)
    }

    /// Lower a type with substitution context applied.
    #[track_caller]
    fn lower_ty(&self, ty: Ty<'gcx>) -> Option<BasicTypeEnum<'llvm>> {
        lower_type(
            self.context,
            self.gcx,
            &self.target_data,
            ty,
            self.current_subst,
        )
    }

    fn abi_policy_for_signature(
        &self,
        sig: &crate::sema::models::LabeledFunctionSignature<'gcx>,
    ) -> abi::AbiPolicy {
        let is_taro_abi = sig.abi.is_none();
        abi::AbiPolicy {
            enable_indirect_returns: is_taro_abi,
            indirect_return_threshold_bytes: self.indirect_return_threshold_bytes,
            enable_indirect_args: is_taro_abi,
            indirect_arg_threshold_bytes: self.indirect_arg_threshold_bytes,
        }
    }

    fn type_layout(&self, ty: Ty<'gcx>) -> Option<abi::TypeLayout> {
        let llvm_ty = self.lower_ty(ty)?;
        let target_triple = self.target_machine.get_triple();
        let target_triple = target_triple.as_str().to_str().unwrap_or("");
        Some(abi::TypeLayout {
            size: self.target_data.get_store_size(&llvm_ty),
            align: self.target_data.get_abi_alignment(&llvm_ty),
            // LLVM 22 uses GlobalISel for AArch64 O0 and SelectionDAG above O0.
            // They assign different overflow stack slots to recursively expanded
            // array aggregates, so direct passing would make debug callers ABI-
            // incompatible with release libraries. Passing those values by
            // address keeps Taro's cross-profile ABI stable while leaving plain
            // scalar and struct values on the normal size-based path.
            force_indirect: target_is_aarch64(target_triple) && llvm_type_contains_array(llvm_ty),
        })
    }

    fn compute_instance_fn_abi(
        &self,
        instance: Instance<'gcx>,
        def_id: hir::DefinitionID,
    ) -> abi::FnAbi<'gcx> {
        let sig = self.gcx.get_signature(def_id);
        let output = if self
            .gcx
            .store
            .synthetic_definitions
            .borrow()
            .get(&def_id)
            .is_some_and(|d| {
                matches!(
                    d.kind,
                    crate::sema::models::SyntheticDefinitionKind::FunctionPointerCall {
                        is_async: true
                    }
                )
            }) {
            self.gcx.async_handle_ty()
        } else if !self.gcx.is_instance_generated(def_id) && self.instance_has_mir_body(instance) {
            let body = self.gcx.get_mir_body(def_id);
            body.locals[body.return_local].ty
        } else {
            sig.output
        };
        let instance_args = instance.args();
        let input_tys: Vec<_> = sig
            .inputs
            .iter()
            .map(|param| self.mono_ty_with_args_if_resolved(param.ty, instance_args))
            .collect();
        let output = self.mono_ty_with_args_if_resolved(output, instance_args);
        let mut fn_abi = abi::compute_fn_abi_from_tys(
            &input_tys,
            output,
            sig.is_variadic,
            |ty| self.type_layout(ty),
            self.abi_policy_for_signature(sig),
        );
        if sig.abi.is_some() {
            self.classify_native_string_arguments(&mut fn_abi);
        }
        fn_abi
    }

    fn compute_fn_pointer_abi(
        &self,
        inputs: &'gcx [Ty<'gcx>],
        output: Ty<'gcx>,
    ) -> abi::FnAbi<'gcx> {
        let input_tys: Vec<_> = inputs
            .iter()
            .map(|ty| self.mono_ty_if_resolved(*ty))
            .collect();
        let output = self.mono_ty_if_resolved(output);
        abi::compute_fn_abi_from_tys(
            &input_tys,
            output,
            false,
            |ty| self.type_layout(ty),
            abi::AbiPolicy {
                enable_indirect_returns: true,
                indirect_return_threshold_bytes: self.indirect_return_threshold_bytes,
                enable_indirect_args: true,
                indirect_arg_threshold_bytes: self.indirect_arg_threshold_bytes,
            },
        )
    }

    fn lower_fn_abi(&self, fn_abi: &abi::FnAbi<'gcx>) -> FunctionType<'llvm> {
        let mut params: Vec<BasicMetadataTypeEnum<'llvm>> =
            Vec::with_capacity(fn_abi.args.len() + 1);
        if matches!(fn_abi.ret.mode, abi::PassMode::Indirect { .. }) {
            params.push(self.context.ptr_type(AddressSpace::default()).into());
        }
        for arg in &fn_abi.args {
            match arg.mode {
                abi::PassMode::Ignore => {}
                abi::PassMode::Direct => {
                    if let Some(ty) = self.lower_ty(arg.ty) {
                        params.push(ty.into());
                    }
                }
                abi::PassMode::Indirect { .. } => {
                    params.push(self.context.ptr_type(AddressSpace::default()).into());
                }
            }
        }

        match fn_abi.ret.mode {
            abi::PassMode::Ignore => self.context.void_type().fn_type(&params, fn_abi.c_variadic),
            abi::PassMode::Direct => match self.lower_ty(fn_abi.ret.ty) {
                Some(ret) => ret.fn_type(&params, fn_abi.c_variadic),
                None => self.context.void_type().fn_type(&params, fn_abi.c_variadic),
            },
            abi::PassMode::Indirect { .. } => {
                self.context.void_type().fn_type(&params, fn_abi.c_variadic)
            }
        }
    }

    fn declare_instances(&mut self) {
        let current_pkg = self.gcx.package_index();
        let instances = self.gcx.specializations_of(current_pkg);
        for instance in instances {
            let def_id = match instance.kind() {
                InstanceKind::Item(def_id) => def_id,
                InstanceKind::Virtual(_) => continue,
            };

            // Skip intrinsic functions - they are handled specially via try_lower_intrinsic_call
            // and don't need to be declared as regular functions.
            if matches!(
                self.gcx.get_signature(def_id).abi,
                Some(hir::Abi::Intrinsic)
            ) {
                continue;
            }

            self.instance_function_with_abi(instance);
        }
    }

    fn static_storage_type(&self, ty: Ty<'gcx>) -> BasicTypeEnum<'llvm> {
        lower_type(
            self.context,
            self.gcx,
            &self.target_data,
            ty,
            GenericArguments::empty(),
        )
        .unwrap_or_else(|| self.context.i8_type().array_type(0).into())
    }

    fn lower_enum_unit_variant_const(
        &mut self,
        ty: Ty<'gcx>,
        ctor_id: hir::DefinitionID,
    ) -> Option<BasicValueEnum<'llvm>> {
        let TyKind::Adt(def, adt_args) = ty.kind() else {
            return None;
        };
        if def.kind != crate::sema::models::AdtKind::Enum {
            return None;
        }

        let enum_def = self.gcx.get_enum_definition(def.id);
        let (variant_index, variant) = enum_def
            .variants
            .iter()
            .enumerate()
            .find(|(_, variant)| variant.ctor_def_id == ctor_id)?;
        if !matches!(variant.kind, crate::sema::models::EnumVariantKind::Unit) {
            return None;
        }

        let layout = self.enum_layout_for(def.id, adt_args);

        // NPO: the unit variant is represented as the all-zero bit pattern.
        if let Some(npo) = layout.npo {
            if variant_index == npo.null_variant {
                let enum_ty = self.lower_ty(ty)?;
                return Some(enum_ty.const_zero().as_basic_value_enum());
            }
            return None;
        }

        let enum_ty = self.lower_ty(ty)?.into_struct_type();
        let mut fields: Vec<_> = enum_ty
            .get_field_types()
            .into_iter()
            .map(|field| field.const_zero())
            .collect();
        fields[0] = layout
            .discr_ty
            .const_int(variant_index as u64, false)
            .as_basic_value_enum();

        Some(enum_ty.const_named_struct(&fields).as_basic_value_enum())
    }

    fn lower_const_value_with_ty(
        &mut self,
        ty: Ty<'gcx>,
        value: ConstValue,
    ) -> Option<BasicValueEnum<'llvm>> {
        match value {
            ConstValue::Bool(v) => Some(
                self.context
                    .bool_type()
                    .const_int(v as u64, false)
                    .as_basic_value_enum(),
            ),
            ConstValue::Rune(v) => Some(
                self.context
                    .i32_type()
                    .const_int(v as u64, false)
                    .as_basic_value_enum(),
            ),
            ConstValue::Bytes(value) => Some(
                value
                    .with_bytes(|b| self.context.const_string(b, false))
                    .as_basic_value_enum(),
            ),
            ConstValue::String(sym) => {
                let ptr = self.lower_string(sym);
                let len = self
                    .usize_ty
                    .const_int(self.gcx.symbol_text(sym).len() as u64, false);
                let struct_ty = self.lower_ty(ty)?.into_struct_type();
                Some(
                    self.string_constant_header(struct_ty, ptr, len)
                        .as_basic_value_enum(),
                )
            }
            ConstValue::Integer(v) => self
                .int_type(ty)
                .map(|(int_ty, _)| int_ty.const_int(v as u64, false).as_basic_value_enum()),
            ConstValue::Float(v) => self
                .float_type(ty)
                .map(|float_ty| float_ty.const_float(v).as_basic_value_enum()),
            ConstValue::Unit => None,
            ConstValue::EnumUnitVariant(ctor_id) => self.lower_enum_unit_variant_const(ty, ctor_id),
            ConstValue::Array(arr) => self.lower_const_array_with_ty(ty, arr),
        }
    }

    fn lower_const_array_with_ty(
        &mut self,
        ty: Ty<'gcx>,
        arr: crate::sema::models::InternedConstArray,
    ) -> Option<BasicValueEnum<'llvm>> {
        let TyKind::Array { element, .. } =
            crate::sema::tycheck::utils::normalize_aliases(self.gcx, ty).kind()
        else {
            return None;
        };
        let elem_llvm_ty = self.lower_ty(element)?;
        let elements = arr.to_vec();
        let mut lowered = Vec::with_capacity(elements.len());
        for elem in elements {
            lowered.push(self.lower_const_value_with_ty(element, elem)?);
        }
        match elem_llvm_ty {
            BasicTypeEnum::IntType(t) => {
                let vals: Vec<_> = lowered.into_iter().map(|v| v.into_int_value()).collect();
                Some(t.const_array(&vals).as_basic_value_enum())
            }
            BasicTypeEnum::FloatType(t) => {
                let vals: Vec<_> = lowered.into_iter().map(|v| v.into_float_value()).collect();
                Some(t.const_array(&vals).as_basic_value_enum())
            }
            BasicTypeEnum::PointerType(t) => {
                let vals: Vec<_> = lowered
                    .into_iter()
                    .map(|v| v.into_pointer_value())
                    .collect();
                Some(t.const_array(&vals).as_basic_value_enum())
            }
            BasicTypeEnum::StructType(t) => {
                let vals: Vec<_> = lowered.into_iter().map(|v| v.into_struct_value()).collect();
                Some(t.const_array(&vals).as_basic_value_enum())
            }
            BasicTypeEnum::ArrayType(t) => {
                let vals: Vec<_> = lowered.into_iter().map(|v| v.into_array_value()).collect();
                Some(t.const_array(&vals).as_basic_value_enum())
            }
            BasicTypeEnum::VectorType(t) => {
                let vals: Vec<_> = lowered.into_iter().map(|v| v.into_vector_value()).collect();
                Some(t.const_array(&vals).as_basic_value_enum())
            }
            BasicTypeEnum::ScalableVectorType(_) => None,
        }
    }

    fn define_local_static_global(&mut self, def_id: hir::DefinitionID) -> PointerValue<'llvm> {
        if let Some(ptr) = self.globals.get(&def_id) {
            return *ptr;
        }

        let ty = self.gcx.get_type(def_id);
        let llvm_ty = self.static_storage_type(ty);
        let name = mangle(self.gcx, def_id);
        let global = self.module.add_global(llvm_ty, None, &name);

        // Even immutable source bindings have writable backing until their
        // one initializer publishes them. No zero value is exposed to source.
        global.set_constant(false);
        global.set_linkage(Linkage::External);
        global.set_initializer(&llvm_ty.const_zero());

        let ptr = global.as_pointer_value();
        self.globals.insert(def_id, ptr);
        // The whole range is a root from startup: zeroed or partially
        // initialized storage only ever holds null or valid managed pointers.
        if self.target_data.get_store_size(&llvm_ty) != 0
            && !self.gc_layout_nodes_for_ty(ty).is_empty()
        {
            let descriptor = self.gc_descriptor_for(ty);
            self.static_gc_roots.push((ptr, descriptor));
        }
        ptr
    }

    fn emit_dispatch_registration_ctor(&mut self) {
        if self
            .module
            .get_function("__taro_register_class_methods")
            .is_none()
            && self
                .module
                .get_function("__taro_register_erased_openings")
                .is_none()
            && self.static_gc_roots.is_empty()
        {
            return;
        }

        let void_ty = self.context.void_type();
        let ptr_ty = self.context.ptr_type(AddressSpace::default());
        let ctor_ty = void_ty.fn_type(&[], false);
        let ctor =
            self.module
                .add_function("__taro_register_dispatch", ctor_ty, Some(Linkage::Internal));
        let entry = self.context.append_basic_block(ctor, "entry");
        let builder = self.context.create_builder();
        builder.position_at_end(entry);

        if let Some(register) = self.module.get_function("__taro_register_class_methods") {
            builder.build_call(register, &[], "").unwrap();
        }
        if let Some(register) = self.module.get_function("__taro_register_erased_openings") {
            builder.build_call(register, &[], "").unwrap();
        }
        if !self.static_gc_roots.is_empty() {
            let register_static = self
                .module
                .get_function("__gc__register_static")
                .unwrap_or_else(|| {
                    self.module.add_function(
                        "__gc__register_static",
                        self.context
                            .void_type()
                            .fn_type(&[ptr_ty.into(), ptr_ty.into()], false),
                        Some(Linkage::External),
                    )
                });
            for (start, descriptor) in &self.static_gc_roots {
                builder
                    .build_call(
                        register_static,
                        &[(*start).into(), (*descriptor).into()],
                        "",
                    )
                    .unwrap();
            }
        }
        builder.build_return(None).unwrap();

        let priority_ty = self.context.i32_type();
        let ctor_entry_ty = self
            .context
            .struct_type(&[priority_ty.into(), ptr_ty.into(), ptr_ty.into()], false);
        let ctor_entry = ctor_entry_ty.const_named_struct(&[
            priority_ty.const_int(65535, false).into(),
            ctor.as_global_value().as_pointer_value().into(),
            ptr_ty.const_null().into(),
        ]);
        let ctors_ty = ctor_entry_ty.array_type(1);
        let ctors = self.module.add_global(ctors_ty, None, "llvm.global_ctors");
        ctors.set_linkage(Linkage::Appending);
        ctors.set_initializer(&ctor_entry_ty.const_array(&[ctor_entry]));
    }

    fn declare_external_static_global(&mut self, def_id: hir::DefinitionID) -> PointerValue<'llvm> {
        if let Some(ptr) = self.globals.get(&def_id) {
            return *ptr;
        }

        let ty = self.gcx.get_type(def_id);
        let llvm_ty = self.static_storage_type(ty);
        let name = mangle(self.gcx, def_id);
        let global = self.module.add_global(llvm_ty, None, &name);
        global.set_linkage(Linkage::External);
        let ptr = global.as_pointer_value();
        self.globals.insert(def_id, ptr);
        ptr
    }

    fn global_variable_address(&mut self, def_id: hir::DefinitionID) -> PointerValue<'llvm> {
        if def_id.package() == self.gcx.package_index() {
            self.define_local_static_global(def_id)
        } else {
            self.declare_external_static_global(def_id)
        }
    }

    fn declare_local_static_globals(&mut self) {
        let output = self.gcx.resolution_output(self.gcx.package_index());
        for (def_id, kind) in output.definition_to_kind.iter() {
            if *kind == DefinitionKind::ModuleVariable {
                self.define_local_static_global(*def_id);
            }
        }
    }

    fn lower_instances(&mut self) -> CompileResult<()> {
        self.declare_local_static_globals();
        let mut emitted = FxHashSet::default();
        // Declaring a function schedules it exactly once. Lowering can declare
        // more functions (closure shims and witness thunks), which join this
        // same worklist without rebuilding a second reachability set.
        loop {
            self.close_class_dispatch()?;
            self.close_erased_openings()?;
            let Some(instance) = self.pending_function_instances.pop() else {
                break;
            };
            // Skip if already compiled by another package
            if self.gcx.is_instance_compiled(instance) {
                continue;
            }

            let def_id = match instance.kind() {
                InstanceKind::Item(def_id) => def_id,
                InstanceKind::Virtual(_) => continue,
            };

            match crate::sema::lowering::erased_opening::plan(self.gcx, def_id, instance.args()) {
                Ok(Some(plan)) => {
                    self.emit_erased_opening(instance, plan)?;
                    self.gcx.mark_instance_compiled(instance);
                    emitted.insert(instance);
                    continue;
                }
                Ok(None) => {}
                Err(reason) => {
                    self.gcx.dcx().emit_error(
                        format!("invalid existential opening specialization: {reason:?}"),
                        None,
                    );
                    return self.gcx.dcx().ok();
                }
            }

            // Skip intrinsic functions - they are handled specially via try_lower_intrinsic_call
            // and don't have MIR bodies.
            if matches!(
                self.gcx.get_signature(def_id).abi,
                Some(hir::Abi::Intrinsic | hir::Abi::C | hir::Abi::Blocking)
            ) {
                continue;
            }

            let initializer_dispatch = self.gcx.store.synthetic_definitions.borrow().get(&def_id).and_then(|definition| {
                if let crate::sema::models::SyntheticDefinitionKind::ClassInitializerDispatch { initializer } = definition.kind { Some(initializer) } else { None }
            });
            let descriptor_class = self.gcx.store.synthetic_definitions.borrow().get(&def_id).and_then(|definition| {
                if let crate::sema::models::SyntheticDefinitionKind::ClassConstructionDescriptor { class } = definition.kind { Some(class) } else { None }
            });
            let object_descriptor = self
                .gcx
                .store
                .synthetic_definitions
                .borrow()
                .get(&def_id)
                .is_some_and(|definition| {
                    matches!(
                        definition.kind,
                        crate::sema::models::SyntheticDefinitionKind::ClassObjectDescriptor { .. }
                    )
                });
            let erased_projection = self
                .gcx
                .store
                .synthetic_definitions
                .borrow()
                .get(&def_id)
                .and_then(|definition| {
                    if let crate::sema::models::SyntheticDefinitionKind::ErasedPayloadReference {
                        ..
                    } = definition.kind
                    {
                        Some(())
                    } else {
                        None
                    }
                });
            if erased_projection.is_some() {
                self.emit_erased_payload_reference(instance)?;
                self.gcx.mark_instance_compiled(instance);
                emitted.insert(instance);
                continue;
            }
            if object_descriptor {
                self.emit_class_object_descriptor(instance)?;
                self.gcx.mark_instance_compiled(instance);
                emitted.insert(instance);
                continue;
            }
            if let Some(class) = descriptor_class {
                let class =
                    instantiate_ty_with_args(self.gcx, self.gcx.get_type(class), instance.args());
                let descriptor = self.class_descriptor(class)?;
                let (function, _) = self.instance_function_with_abi(instance);
                let builder = self.context.create_builder();
                builder.position_at_end(self.context.append_basic_block(function, "class_context"));
                builder.build_return(Some(&descriptor)).unwrap();
                self.gcx.mark_instance_compiled(instance);
                emitted.insert(instance);
                continue;
            }
            if let Some(source) = initializer_dispatch {
                self.emit_class_initializer_dispatch(instance, source)?;
                self.gcx.mark_instance_compiled(instance);
                emitted.insert(instance);
                continue;
            }

            if self.try_emit_gc_class_factory(instance)? {
                self.gcx.mark_instance_compiled(instance);
                emitted.insert(instance);
                continue;
            }
            if !self.instance_has_mir_body(instance) {
                continue;
            }

            let body = { self.gcx.get_gc_instance_mir_body(instance)? };
            self.lower_body(instance, body)?;

            // Mark as compiled so other packages don't duplicate work
            self.gcx.mark_instance_compiled(instance);

            emitted.insert(instance);
        }
        self.gcx
            .cache_emitted_instances(self.gcx.package_index(), emitted);
        self.emit_class_registration_ctor()?;
        self.emit_erased_opening_ctor();
        c_extensions::finalize(self)?;
        Ok(())
    }

    fn instance_has_mir_body(&self, instance: Instance<'gcx>) -> bool {
        let InstanceKind::Item(def_id) = instance.kind() else {
            return false;
        };
        if self.gcx.is_instance_generated(def_id) {
            return true;
        }
        let packages = self.gcx.store.mir_packages.borrow();
        packages
            .get(&def_id.package())
            .is_some_and(|pkg| pkg.functions.contains_key(&def_id))
    }

    fn env_globals_define_here(&self) -> bool {
        !matches!(
            self.gcx.config.kind,
            crate::compile::config::PackageKind::Library
        )
    }

    fn get_or_create_env_argc_global(&mut self) -> PointerValue<'llvm> {
        if let Some(ptr) = self.env_argc_storage {
            return ptr;
        }

        let global = self
            .module
            .get_global(ENV_ARGC_GLOBAL_NAME)
            .unwrap_or_else(|| {
                let global = self
                    .module
                    .add_global(self.usize_ty, None, ENV_ARGC_GLOBAL_NAME);
                global.set_linkage(Linkage::External);
                if self.env_globals_define_here() {
                    global.set_initializer(&self.usize_ty.const_zero());
                }
                global
            });
        let ptr = global.as_pointer_value();
        self.env_argc_storage = Some(ptr);
        ptr
    }

    fn get_or_create_env_argv_global(&mut self) -> PointerValue<'llvm> {
        if let Some(ptr) = self.env_argv_storage {
            return ptr;
        }

        let ptr_ty = self.context.ptr_type(AddressSpace::default());
        let global = self
            .module
            .get_global(ENV_ARGV_GLOBAL_NAME)
            .unwrap_or_else(|| {
                let global = self.module.add_global(ptr_ty, None, ENV_ARGV_GLOBAL_NAME);
                global.set_linkage(Linkage::External);
                if self.env_globals_define_here() {
                    global.set_initializer(&ptr_ty.const_null());
                }
                global
            });
        let ptr = global.as_pointer_value();
        self.env_argv_storage = Some(ptr);
        ptr
    }

    fn store_process_args_from_main(
        &mut self,
        builder: &Builder<'llvm>,
        argc: IntValue<'llvm>,
        argv: PointerValue<'llvm>,
    ) {
        let argc_global = self.get_or_create_env_argc_global();
        let argv_global = self.get_or_create_env_argv_global();
        let argc = if argc.get_type() == self.usize_ty {
            argc
        } else {
            builder
                .build_int_cast(argc, self.usize_ty, "argc_to_usize")
                .unwrap()
        };

        builder.build_store(argc_global, argc).unwrap();
        builder.build_store(argv_global, argv).unwrap();
    }

    /// Assert that an entry/test function can be called with an empty argument
    /// list, as the shims below do. Sema restricts these functions to
    /// `() -> void`; a `Result`-returning `main` is reached through a
    /// generated `() -> int32` wrapper. Their computed ABI must not expect any
    /// parameters — in particular no hidden sret pointer, which the callee
    /// would otherwise write its return through while reading garbage as the
    /// destination.
    fn assert_entry_abi_takes_no_args(&self, fn_abi: &abi::FnAbi<'gcx>, what: &str) {
        assert!(
            !matches!(fn_abi.ret.mode, abi::PassMode::Indirect { .. }),
            "{what} must not return indirectly (sret); it returns `void` or an `int32` status"
        );
        assert!(
            fn_abi
                .args
                .iter()
                .all(|arg| matches!(arg.mode, abi::PassMode::Ignore)),
            "{what} must not take ABI arguments; sema restricts it to no parameters"
        );
    }

    /// Emit the `taro_start` / `main` entry shim for a normal (non-test) binary.
    ///
    /// `taro_start` invokes the user's `main` function via an `invoke` instruction so
    /// that any Taro panic that unwinds past it is caught by the landing pad below.
    /// The landing pad is a catch-all (null filter list, `cleanup=false`) that calls
    /// `__rt__panic_abort_unwind`, which prints the panic report and exits.
    ///
    /// A thin `main` wrapper is also emitted so the linker finds a conventional
    /// entry point; it simply tail-calls `taro_start` and forwards its return value.
    ///
    /// For `func main() -> Result[(), E]` the package entry is the generated
    /// `main$result_entry` wrapper (see `thir::main_result`), which reports an
    /// error itself and returns the `int32` exit status forwarded here.
    fn emit_start_shim(&mut self, package: &mir::MirPackage<'gcx>) {
        let Some(entry) = package.entry else {
            return;
        };
        // Entry point is always a concrete instance with no generic args
        let entry_instance = Instance::item(entry, GenericArguments::empty());
        let Some((user_fn, entry_fn_abi)) = self.functions.get(&entry_instance).cloned() else {
            return;
        };
        self.assert_entry_abi_takes_no_args(&entry_fn_abi, "entry point `main`");
        let entry_sig = self.gcx.get_signature(entry);
        let finish_main_fn = self.declare_executor_finish_main_fn();

        let i32_ty = self.context.i32_type();
        let start_ty = i32_ty.fn_type(&[], false);
        let start_fn = self.module.add_function("taro_start", start_ty, None);
        let personality = self.eh_personality_fn();
        start_fn.set_personality_function(personality);

        let builder = self.context.create_builder();
        let bb_entry = self.context.append_basic_block(start_fn, "entry");
        let bb_ret = self.context.append_basic_block(start_fn, "ret");
        let bb_panic = self.context.append_basic_block(start_fn, "panic");
        builder.position_at_end(bb_entry);
        let install_stack_guard_fn = self.declare_install_stack_guard_fn();
        builder
            .build_call(install_stack_guard_fn, &[], "install_stack_guard")
            .unwrap();
        let call = builder
            .build_invoke(user_fn, &[], bb_ret, bb_panic, "call_main")
            .unwrap();

        builder.position_at_end(bb_ret);
        builder
            .build_call(finish_main_fn, &[], "finish_main")
            .unwrap();

        let exit_code = match (entry_sig.output.kind(), call.try_as_basic_value().basic()) {
            (TyKind::Infer(_) | TyKind::Error, _) => {
                i32_ty.const_int(0, false).as_basic_value_enum()
            }
            (TyKind::Tuple(items), _) if items.is_empty() => {
                i32_ty.const_int(0, false).as_basic_value_enum()
            }
            (TyKind::Bool, Some(val)) => {
                let int = builder
                    .build_int_z_extend_or_bit_cast(val.into_int_value(), i32_ty, "bool_to_i32")
                    .unwrap();
                int.as_basic_value_enum()
            }
            (TyKind::Int(_) | TyKind::UInt(_) | TyKind::Rune, Some(val)) => {
                let int_val = val.into_int_value();
                let cast = builder
                    .build_int_cast(int_val, i32_ty, "int_to_i32")
                    .unwrap();
                cast.as_basic_value_enum()
            }
            (TyKind::Float(_), Some(val)) => builder
                .build_float_to_signed_int(val.into_float_value(), i32_ty, "float_to_i32")
                .unwrap()
                .as_basic_value_enum(),
            (TyKind::Pointer(..) | TyKind::Reference(..), Some(val)) => {
                let ptr = val.into_pointer_value();
                let int64 = builder
                    .build_ptr_to_int(ptr, self.context.i64_type(), "ptr_to_int")
                    .unwrap();
                builder
                    .build_int_cast(int64, i32_ty, "ptr_to_i32")
                    .unwrap()
                    .as_basic_value_enum()
            }
            (_, Some(_)) => i32_ty.const_int(0, false).as_basic_value_enum(),
            _ => i32_ty.const_int(0, false).as_basic_value_enum(),
        };

        let _ = builder.build_return(Some(&exit_code)).unwrap();

        builder.position_at_end(bb_panic);
        let catch_all = self
            .context
            .ptr_type(AddressSpace::default())
            .const_null()
            .as_basic_value_enum();
        let landing = builder
            .build_landing_pad(
                self.eh_landingpad_ty(),
                personality,
                &[catch_all],
                false,
                "start_lpad",
            )
            .unwrap()
            .into_struct_value();
        let exception_ptr = builder
            .build_extract_value(landing, 0, "panic_exc_ptr")
            .unwrap()
            .into_pointer_value();
        let abort_unwind = self.get_panic_abort_unwind_fn();
        let _ = builder
            .build_call(
                abort_unwind,
                &[BasicMetadataValueEnum::from(
                    exception_ptr.as_basic_value_enum(),
                )],
                "panic_abort",
            )
            .unwrap();
        let _ = builder.build_unreachable().unwrap();

        // Provide a conventional `main` that forwards to `taro_start` for easier linking.
        let ptr_ty = self.context.ptr_type(AddressSpace::default());
        let main_ty = i32_ty.fn_type(&[i32_ty.into(), ptr_ty.into()], false);
        let main_fn = self.module.add_function("main", main_ty, None);
        let main_builder = self.context.create_builder();
        let main_bb = self.context.append_basic_block(main_fn, "entry");
        main_builder.position_at_end(main_bb);
        let argc = main_fn
            .get_nth_param(0)
            .expect("main argc parameter missing")
            .into_int_value();
        let argv = main_fn
            .get_nth_param(1)
            .expect("main argv parameter missing")
            .into_pointer_value();
        self.get_or_create_env_argc_global();
        self.get_or_create_env_argv_global();
        self.store_process_args_from_main(&main_builder, argc, argv);
        let start_call = main_builder
            .build_call(start_fn, &[], "call_start")
            .unwrap();
        let main_ret = start_call
            .try_as_basic_value()
            .basic()
            .map(|v| v.into_int_value())
            .unwrap_or_else(|| i32_ty.const_int(0, false));
        let _ = main_builder.build_return(Some(&main_ret)).unwrap();
    }

    /// Emit the `taro_start` / `main` entry shim for test mode.
    ///
    /// Instead of a normal entry point this generates a test runner that:
    ///
    /// 1. Prints `running N tests`.
    /// 2. For each `@test` function:
    ///    - If `@skip`, print `SKIPPED` and move on without calling the function.
    ///    - Otherwise call the function via `__rt__test_call_fn`, which wraps the
    ///      call in `catch_unwind` and returns `true` if the function panicked.
    ///    - Ask the runtime to combine the panic flag with `@expectPanic` and
    ///      its optional expected-message substring.
    ///    - Print the result, then let the runtime report unexpected/mismatched
    ///      panic details and reset state before the next test runs.
    /// 3. Print a `test result:` summary line and exit with 0 (all passed) or 101
    ///    (at least one failure).
    ///
    /// Panic interception works because `__rt__panic_unwind_at` checks the
    /// `IN_TEST_HARNESS` thread-local (set by `__rt__test_call_fn`) and uses
    /// `panic_any` instead of `_Unwind_ForcedUnwind` when running inside a test,
    /// making the panic catchable by `catch_unwind`.
    fn emit_test_harness(&mut self, tests: &[crate::compile::test_collector::TestCase]) {
        let i32_ty = self.context.i32_type();
        let i8_ty = self.context.i8_type();
        let ptr_ty = self.context.ptr_type(AddressSpace::default());

        // Declare runtime/libc helpers
        let puts_fn = self.declare_puts_fn();
        let printf_fn = self.declare_printf_fn();
        let test_call_fn = self.declare_test_call_fn();
        let test_panic_status_fn = self.declare_test_panic_status_fn();
        let test_panic_finish_fn = self.declare_test_panic_finish_fn();
        let test_prepare_result_fn = self.declare_test_prepare_result_fn();
        let async_run_root_fn = self.declare_async_run_root_fn();
        let finish_rootless_fn = self.declare_executor_finish_rootless_fn();
        let abort_rootless_fn = self.declare_executor_abort_rootless_fn();

        // --- taro_start function ---
        let start_ty = i32_ty.fn_type(&[], false);
        let start_fn = self.module.add_function("taro_start", start_ty, None);

        let builder = self.context.create_builder();
        let entry_bb = self.context.append_basic_block(start_fn, "entry");
        builder.position_at_end(entry_bb);

        let install_stack_guard_fn = self.declare_install_stack_guard_fn();
        builder
            .build_call(install_stack_guard_fn, &[], "install_stack_guard")
            .unwrap();

        // Counters: passed, failed, skipped (alloca in entry)
        let passed_ptr = builder.build_alloca(i32_ty, "passed").unwrap();
        let failed_ptr = builder.build_alloca(i32_ty, "failed").unwrap();
        let skipped_ptr = builder.build_alloca(i32_ty, "skipped").unwrap();
        builder
            .build_store(passed_ptr, i32_ty.const_zero())
            .unwrap();
        builder
            .build_store(failed_ptr, i32_ty.const_zero())
            .unwrap();
        builder
            .build_store(skipped_ptr, i32_ty.const_zero())
            .unwrap();

        let mut fn_ptrs: Vec<PointerValue<'llvm>> = Vec::new();
        let mut prefix_ptrs: Vec<PointerValue<'llvm>> = Vec::new();
        let mut skipped_msg_ptrs: Vec<PointerValue<'llvm>> = Vec::new();
        let mut expect_flags: Vec<u8> = Vec::new();
        let mut expected_panic_message_ptrs: Vec<PointerValue<'llvm>> = Vec::new();
        let mut expected_panic_message_lens: Vec<u64> = Vec::new();
        let mut skipped_flags: Vec<u8> = Vec::new();

        for (idx, test) in tests.iter().enumerate() {
            let test_instance = Instance::item(test.id, GenericArguments::empty());
            let Some((test_fn, test_fn_abi)) = self.functions.get(&test_instance).cloned() else {
                continue;
            };

            let prefix = format!("test {} ... ", test.display_name);
            let prefix_global = self.build_global_cstring(&prefix, &format!("test_prefix_{}", idx));
            prefix_ptrs.push(prefix_global);

            let skipped_msg = match &test.skip_reason {
                Some(r) => format!("SKIPPED ({})\n", r),
                None => "SKIPPED\n".to_string(),
            };
            let skipped_global =
                self.build_global_cstring(&skipped_msg, &format!("skipped_msg_{}", idx));
            skipped_msg_ptrs.push(skipped_global);

            let fn_ptr = if test.is_async {
                self.emit_async_test_wrapper(test_fn, &test_fn_abi, async_run_root_fn, idx)
            } else {
                self.emit_sync_test_wrapper(test_fn, &test_fn_abi, finish_rootless_fn, idx)
            };
            fn_ptrs.push(fn_ptr);
            expect_flags.push(if test.expect_panic { 1 } else { 0 });
            let expected_message = test.expected_panic_message.as_deref().unwrap_or("");
            expected_panic_message_ptrs.push(self.build_global_cstring(
                expected_message,
                &format!("test_expected_panic_message_{idx}"),
            ));
            expected_panic_message_lens.push(expected_message.len() as u64);
            skipped_flags.push(if test.skipped { 1 } else { 0 });
        }

        let test_count = fn_ptrs.len() as u64;

        // Print header
        let header = format!(
            "\nrunning {} test{}\n",
            test_count,
            if test_count == 1 { "" } else { "s" }
        );
        let header_global = self.build_global_cstring(&header, "test_header");
        builder
            .build_call(puts_fn, &[header_global.into()], "")
            .unwrap();

        let ok_msg = self.build_global_cstring("ok\n", "test_ok_msg");
        let fail_panic_msg =
            self.build_global_cstring("FAILED (panicked)\n", "test_fail_panic_msg");
        let fail_expected_msg = self.build_global_cstring(
            "FAILED (expected panic but test completed normally)\n",
            "test_fail_expected_msg",
        );
        let fail_panic_message_msg = self.build_global_cstring(
            "FAILED (panic message mismatch)\n",
            "test_fail_panic_message_msg",
        );
        let fail_subtest_msg =
            self.build_global_cstring("FAILED (subtest failed)\n", "test_fail_subtest_msg");
        let string_fmt = self.build_global_cstring("%s", "test_string_fmt");

        if test_count > 0 {
            let fn_table = self.build_global_ptr_array(&fn_ptrs, "test_fn_table");
            let prefix_table = self.build_global_ptr_array(&prefix_ptrs, "test_prefix_table");
            let skipped_msg_table =
                self.build_global_ptr_array(&skipped_msg_ptrs, "test_skipped_msg_table");
            let expect_table = self.build_global_i8_array(&expect_flags, "test_expect_table");
            let expected_panic_message_table = self.build_global_ptr_array(
                &expected_panic_message_ptrs,
                "test_expected_panic_message_table",
            );
            let expected_panic_message_len_table = self.build_global_usize_array(
                &expected_panic_message_lens,
                "test_expected_panic_message_len_table",
            );
            let skipped_table = self.build_global_i8_array(&skipped_flags, "test_skipped_table");

            let idx_ptr = builder.build_alloca(self.usize_ty, "test_idx").unwrap();
            builder
                .build_store(idx_ptr, self.usize_ty.const_zero())
                .unwrap();

            let fn_table_ty = ptr_ty.array_type(test_count as u32);
            let prefix_table_ty = ptr_ty.array_type(test_count as u32);
            let skipped_msg_table_ty = ptr_ty.array_type(test_count as u32);
            let expect_table_ty = i8_ty.array_type(test_count as u32);
            let expected_panic_message_table_ty = ptr_ty.array_type(test_count as u32);
            let expected_panic_message_len_table_ty = self.usize_ty.array_type(test_count as u32);
            let skipped_table_ty = i8_ty.array_type(test_count as u32);

            let loop_cond = self.context.append_basic_block(start_fn, "test_loop_cond");
            let loop_body = self.context.append_basic_block(start_fn, "test_loop_body");
            let loop_skipped = self
                .context
                .append_basic_block(start_fn, "test_loop_skipped");
            let loop_run = self.context.append_basic_block(start_fn, "test_loop_run");
            let loop_next = self.context.append_basic_block(start_fn, "test_loop_next");
            let result_bb = self.context.append_basic_block(start_fn, "result");

            builder.build_unconditional_branch(loop_cond).unwrap();

            builder.position_at_end(loop_cond);
            let idx = builder
                .build_load(self.usize_ty, idx_ptr, "test_idx")
                .unwrap()
                .into_int_value();
            let in_range = builder
                .build_int_compare(
                    IntPredicate::ULT,
                    idx,
                    self.usize_ty.const_int(test_count, false),
                    "test_idx_in_range",
                )
                .unwrap();
            builder
                .build_conditional_branch(in_range, loop_body, result_bb)
                .unwrap();

            builder.position_at_end(loop_body);
            let zero = self.usize_ty.const_zero();

            let prefix_ptr_ptr = unsafe {
                builder
                    .build_gep(
                        prefix_table_ty,
                        prefix_table,
                        &[zero, idx],
                        "test_prefix_ptr_ptr",
                    )
                    .unwrap()
            };
            let prefix_ptr = builder
                .build_load(ptr_ty, prefix_ptr_ptr, "test_prefix_ptr")
                .unwrap()
                .into_pointer_value();
            builder
                .build_call(
                    printf_fn,
                    &[string_fmt.into(), prefix_ptr.into()],
                    "test_prefix_print",
                )
                .unwrap();

            let skipped_flag_ptr = unsafe {
                builder
                    .build_gep(
                        skipped_table_ty,
                        skipped_table,
                        &[zero, idx],
                        "test_skipped_flag_ptr",
                    )
                    .unwrap()
            };
            let skipped_flag = builder
                .build_load(i8_ty, skipped_flag_ptr, "test_skipped_flag")
                .unwrap()
                .into_int_value();
            let is_skipped = builder
                .build_int_compare(
                    IntPredicate::NE,
                    skipped_flag,
                    i8_ty.const_zero(),
                    "test_is_skipped",
                )
                .unwrap();
            builder
                .build_conditional_branch(is_skipped, loop_skipped, loop_run)
                .unwrap();

            builder.position_at_end(loop_skipped);
            let skipped_msg_ptr_ptr = unsafe {
                builder
                    .build_gep(
                        skipped_msg_table_ty,
                        skipped_msg_table,
                        &[zero, idx],
                        "test_skipped_msg_ptr_ptr",
                    )
                    .unwrap()
            };
            let skipped_msg_ptr = builder
                .build_load(ptr_ty, skipped_msg_ptr_ptr, "test_skipped_msg_ptr")
                .unwrap()
                .into_pointer_value();
            builder
                .build_call(
                    printf_fn,
                    &[string_fmt.into(), skipped_msg_ptr.into()],
                    "test_skipped_print",
                )
                .unwrap();
            self.increment_counter(&builder, skipped_ptr, i32_ty);
            builder.build_unconditional_branch(loop_next).unwrap();

            builder.position_at_end(loop_run);
            let fn_ptr_ptr = unsafe {
                builder
                    .build_gep(fn_table_ty, fn_table, &[zero, idx], "test_fn_ptr_ptr")
                    .unwrap()
            };
            let fn_ptr = builder
                .build_load(ptr_ty, fn_ptr_ptr, "test_fn_ptr")
                .unwrap()
                .into_pointer_value();
            let panicked = builder
                .build_call(test_call_fn, &[fn_ptr.into()], "test_panicked")
                .unwrap()
                .try_as_basic_value()
                .basic()
                .unwrap()
                .into_int_value();

            builder
                .build_call(abort_rootless_fn, &[], "test_executor_abort")
                .unwrap();

            let expect_flag_ptr = unsafe {
                builder
                    .build_gep(
                        expect_table_ty,
                        expect_table,
                        &[zero, idx],
                        "test_expect_flag_ptr",
                    )
                    .unwrap()
            };
            let expect_flag = builder
                .build_load(i8_ty, expect_flag_ptr, "test_expect_flag")
                .unwrap()
                .into_int_value();
            let expect_panic = builder
                .build_int_compare(
                    IntPredicate::NE,
                    expect_flag,
                    i8_ty.const_zero(),
                    "test_expect_panic",
                )
                .unwrap();

            let expected_message_ptr_ptr = unsafe {
                builder
                    .build_gep(
                        expected_panic_message_table_ty,
                        expected_panic_message_table,
                        &[zero, idx],
                        "test_expected_panic_message_ptr_ptr",
                    )
                    .unwrap()
            };
            let expected_message_ptr = builder
                .build_load(
                    ptr_ty,
                    expected_message_ptr_ptr,
                    "test_expected_panic_message_ptr",
                )
                .unwrap()
                .into_pointer_value();
            let expected_message_len_ptr = unsafe {
                builder
                    .build_gep(
                        expected_panic_message_len_table_ty,
                        expected_panic_message_len_table,
                        &[zero, idx],
                        "test_expected_panic_message_len_ptr",
                    )
                    .unwrap()
            };
            let expected_message_len = builder
                .build_load(
                    self.usize_ty,
                    expected_message_len_ptr,
                    "test_expected_panic_message_len",
                )
                .unwrap()
                .into_int_value();

            let panic_status = builder
                .build_call(
                    test_panic_status_fn,
                    &[
                        panicked.into(),
                        expect_panic.into(),
                        expected_message_ptr.into(),
                        expected_message_len.into(),
                    ],
                    "test_panic_status",
                )
                .unwrap()
                .try_as_basic_value()
                .basic()
                .unwrap()
                .into_int_value();
            let passed_case = builder
                .build_int_compare(
                    IntPredicate::EQ,
                    panic_status,
                    i8_ty.const_zero(),
                    "test_passed",
                )
                .unwrap();
            let missing_panic = builder
                .build_int_compare(
                    IntPredicate::EQ,
                    panic_status,
                    i8_ty.const_int(2, false),
                    "test_missing_panic",
                )
                .unwrap();
            let panic_message_mismatch = builder
                .build_int_compare(
                    IntPredicate::EQ,
                    panic_status,
                    i8_ty.const_int(3, false),
                    "test_panic_message_mismatch",
                )
                .unwrap();
            let subtest_failed = builder
                .build_int_compare(
                    IntPredicate::EQ,
                    panic_status,
                    i8_ty.const_int(4, false),
                    "test_subtest_failed",
                )
                .unwrap();
            let base_fail_msg = builder
                .build_select(
                    missing_panic,
                    fail_expected_msg,
                    fail_panic_msg,
                    "test_base_fail_msg",
                )
                .unwrap()
                .into_pointer_value();
            let fail_msg_with_mismatch = builder
                .build_select(
                    panic_message_mismatch,
                    fail_panic_message_msg,
                    base_fail_msg,
                    "test_fail_msg_with_mismatch",
                )
                .unwrap()
                .into_pointer_value();
            let fail_msg = builder
                .build_select(
                    subtest_failed,
                    fail_subtest_msg,
                    fail_msg_with_mismatch,
                    "test_fail_msg",
                )
                .unwrap()
                .into_pointer_value();
            let result_msg = builder
                .build_select(passed_case, ok_msg, fail_msg, "test_result_msg")
                .unwrap();
            builder
                .build_call(
                    test_prepare_result_fn,
                    &[prefix_ptr.into()],
                    "test_prepare_result",
                )
                .unwrap();
            builder
                .build_call(
                    printf_fn,
                    &[string_fmt.into(), result_msg.into()],
                    "test_result_print",
                )
                .unwrap();
            builder
                .build_call(
                    test_panic_finish_fn,
                    &[
                        panic_status.into(),
                        expected_message_ptr.into(),
                        expected_message_len.into(),
                    ],
                    "test_panic_finish",
                )
                .unwrap();

            let pass_inc = builder
                .build_int_z_extend(passed_case, i32_ty, "test_pass_inc")
                .unwrap();
            let failed_case = builder.build_not(passed_case, "test_failed_case").unwrap();
            let fail_inc = builder
                .build_int_z_extend(failed_case, i32_ty, "test_fail_inc")
                .unwrap();

            let cur_passed = builder
                .build_load(i32_ty, passed_ptr, "test_cur_passed")
                .unwrap()
                .into_int_value();
            let next_passed = builder
                .build_int_add(cur_passed, pass_inc, "test_next_passed")
                .unwrap();
            builder.build_store(passed_ptr, next_passed).unwrap();

            let cur_failed = builder
                .build_load(i32_ty, failed_ptr, "test_cur_failed")
                .unwrap()
                .into_int_value();
            let next_failed = builder
                .build_int_add(cur_failed, fail_inc, "test_next_failed")
                .unwrap();
            builder.build_store(failed_ptr, next_failed).unwrap();
            builder.build_unconditional_branch(loop_next).unwrap();

            builder.position_at_end(loop_next);
            let next_idx = builder
                .build_int_add(idx, self.usize_ty.const_int(1, false), "test_idx_next")
                .unwrap();
            builder.build_store(idx_ptr, next_idx).unwrap();
            builder.build_unconditional_branch(loop_cond).unwrap();

            builder.position_at_end(result_bb);
        } else {
            let result_bb = self.context.append_basic_block(start_fn, "result");
            builder.build_unconditional_branch(result_bb).unwrap();
            builder.position_at_end(result_bb);
        }

        // --- Summary ---
        let passed = builder.build_load(i32_ty, passed_ptr, "p_final").unwrap();
        let failed = builder.build_load(i32_ty, failed_ptr, "f_final").unwrap();
        let skipped = builder.build_load(i32_ty, skipped_ptr, "s_final").unwrap();

        let failed_int = failed.into_int_value();
        let has_failures = builder
            .build_int_compare(
                IntPredicate::UGT,
                failed_int,
                i32_ty.const_zero(),
                "has_fail",
            )
            .unwrap();

        let ok_str = self.build_global_cstring("ok", "str_ok");
        let fail_str = self.build_global_cstring("FAILED", "str_fail");
        let result_str = builder
            .build_select(has_failures, fail_str, ok_str, "result_str")
            .unwrap();

        let fmt = self.build_global_cstring(
            "\ntest result: %s. %d passed; %d failed; %d skipped\n\n",
            "summary_fmt",
        );
        builder
            .build_call(
                printf_fn,
                &[
                    fmt.into(),
                    result_str.into(),
                    passed.into(),
                    failed.into(),
                    skipped.into(),
                ],
                "",
            )
            .unwrap();

        // Exit code: 0 if no failures, 101 if any
        let exit_code = builder
            .build_select(
                has_failures,
                i32_ty.const_int(101, false),
                i32_ty.const_zero(),
                "exit_code",
            )
            .unwrap();
        builder.build_return(Some(&exit_code)).unwrap();

        // Wrapper main()
        let ptr_ty = self.context.ptr_type(AddressSpace::default());
        let main_ty = i32_ty.fn_type(&[i32_ty.into(), ptr_ty.into()], false);
        let main_fn = self.module.add_function("main", main_ty, None);
        let main_bb = self.context.append_basic_block(main_fn, "entry");
        let mb = self.context.create_builder();
        mb.position_at_end(main_bb);
        let argc = main_fn
            .get_nth_param(0)
            .expect("main argc parameter missing")
            .into_int_value();
        let argv = main_fn
            .get_nth_param(1)
            .expect("main argv parameter missing")
            .into_pointer_value();
        self.get_or_create_env_argc_global();
        self.get_or_create_env_argv_global();
        self.store_process_args_from_main(&mb, argc, argv);
        let ret = mb
            .build_call(start_fn, &[], "ret")
            .unwrap()
            .try_as_basic_value()
            .basic()
            .map(|v| v.into_int_value())
            .unwrap_or_else(|| i32_ty.const_int(0, false));
        mb.build_return(Some(&ret)).unwrap();
    }

    /// Adapt benchmark functions to the runtime's measurement callback, then
    /// invoke the standard-library reporter after the callback has returned.
    fn emit_bench_harness(
        &mut self,
        benchmarks: &[crate::compile::bench_collector::BenchmarkCase],
    ) {
        let i32_ty = self.context.i32_type();
        let ptr_ty = self.context.ptr_type(AddressSpace::default());
        let measure_case_fn = self.declare_bench_measure_case_fn();
        let report_id = self
            .gcx
            .std_item_def(hir::StdItem::BenchmarkReport)
            .expect("benchmark report language item");
        let (report_fn, report_abi) =
            self.instance_function_with_abi(Instance::item(report_id, GenericArguments::empty()));
        let TyKind::Pointer(measurement_ty, _) = report_abi.args[1].ty.kind() else {
            panic!("benchmark report must accept a pointer to its measurement");
        };
        let measurement_ty = self
            .lower_ty(measurement_ty)
            .expect("benchmark measurement must have a runtime representation");
        let finish_rootless_fn = self.declare_executor_finish_rootless_fn();
        let abort_rootless_fn = self.declare_executor_abort_rootless_fn();

        let start_ty = i32_ty.fn_type(&[], false);
        let start_fn = self.module.add_function("taro_start", start_ty, None);
        let builder = self.context.create_builder();
        let entry = self.context.append_basic_block(start_fn, "entry");
        builder.position_at_end(entry);

        let install_stack_guard_fn = self.declare_install_stack_guard_fn();
        builder
            .build_call(install_stack_guard_fn, &[], "install_stack_guard")
            .unwrap();

        let measurement = builder
            .build_alloca(measurement_ty, "bench_measurement")
            .unwrap();
        let failures = builder.build_alloca(i32_ty, "bench_failures").unwrap();
        builder.build_store(failures, i32_ty.const_zero()).unwrap();

        for (index, benchmark) in benchmarks.iter().enumerate() {
            let instance = Instance::item(benchmark.id, GenericArguments::empty());
            let Some((function, function_abi)) = self.functions.get(&instance).cloned() else {
                continue;
            };
            let wrapper =
                self.emit_bench_wrapper(function, &function_abi, finish_rootless_fn, index);

            let name =
                self.build_global_cstring(&benchmark.display_name, &format!("bench_name_{index}"));
            let encoded_tags = benchmark.tags.join("\0");
            let tags = self.build_global_cstring(&encoded_tags, &format!("bench_tags_{index}"));
            let reason_text = benchmark.skip_reason.as_deref().unwrap_or("");
            let reason = self.build_global_cstring(reason_text, &format!("bench_reason_{index}"));

            let name_len = self
                .usize_ty
                .const_int(benchmark.display_name.len() as u64, false);
            let skipped = self
                .context
                .bool_type()
                .const_int(u64::from(benchmark.skipped), false);
            let outcome = builder
                .build_call(
                    measure_case_fn,
                    &[
                        wrapper.into(),
                        name.into(),
                        name_len.into(),
                        skipped.into(),
                        measurement.into(),
                    ],
                    "bench_measurement_status",
                )
                .unwrap()
                .try_as_basic_value()
                .basic()
                .expect("benchmark measurement returns a status")
                .into_int_value();
            builder
                .build_call(abort_rootless_fn, &[], "bench_executor_abort")
                .unwrap();
            let failed = builder
                .build_call(
                    report_fn,
                    &[
                        outcome.into(),
                        measurement.into(),
                        name.into(),
                        name_len.into(),
                        tags.into(),
                        self.usize_ty
                            .const_int(encoded_tags.len() as u64, false)
                            .into(),
                        skipped.into(),
                        reason.into(),
                        self.usize_ty
                            .const_int(reason_text.len() as u64, false)
                            .into(),
                    ],
                    "bench_case_status",
                )
                .unwrap()
                .try_as_basic_value()
                .basic()
                .expect("benchmark reporter returns a status")
                .into_int_value();
            let current = builder
                .build_load(i32_ty, failures, "bench_failure_count")
                .unwrap()
                .into_int_value();
            let failed = builder
                .build_int_z_extend(failed, i32_ty, "bench_failed_i32")
                .unwrap();
            let updated = builder
                .build_int_add(current, failed, "bench_failure_count_next")
                .unwrap();
            builder.build_store(failures, updated).unwrap();
        }

        let failures = builder
            .build_load(i32_ty, failures, "bench_failures_final")
            .unwrap()
            .into_int_value();
        let has_failures = builder
            .build_int_compare(
                IntPredicate::NE,
                failures,
                i32_ty.const_zero(),
                "bench_has_failures",
            )
            .unwrap();
        let exit_code = builder
            .build_select(
                has_failures,
                i32_ty.const_int(101, false),
                i32_ty.const_zero(),
                "bench_exit_code",
            )
            .unwrap()
            .into_int_value();
        builder.build_return(Some(&exit_code)).unwrap();

        // Keep argv available to setup/cleanup code in benchmark functions,
        // matching normal programs and the test harness.
        let main_ty = i32_ty.fn_type(&[i32_ty.into(), ptr_ty.into()], false);
        let main_fn = self.module.add_function("main", main_ty, None);
        let main_entry = self.context.append_basic_block(main_fn, "entry");
        let main_builder = self.context.create_builder();
        main_builder.position_at_end(main_entry);
        let argc = main_fn
            .get_nth_param(0)
            .expect("main argc parameter missing")
            .into_int_value();
        let argv = main_fn
            .get_nth_param(1)
            .expect("main argv parameter missing")
            .into_pointer_value();
        self.get_or_create_env_argc_global();
        self.get_or_create_env_argv_global();
        self.store_process_args_from_main(&main_builder, argc, argv);
        let status = main_builder
            .build_call(start_fn, &[], "bench_status")
            .unwrap()
            .try_as_basic_value()
            .basic()
            .expect("benchmark start returns a status")
            .into_int_value();
        main_builder.build_return(Some(&status)).unwrap();
    }

    fn declare_bench_measure_case_fn(&self) -> FunctionValue<'llvm> {
        let ptr_ty = self.context.ptr_type(AddressSpace::default());
        let function_type = self.context.i8_type().fn_type(
            &[
                ptr_ty.into(),
                ptr_ty.into(),
                self.usize_ty.into(),
                self.context.bool_type().into(),
                ptr_ty.into(),
            ],
            false,
        );
        self.module
            .get_function("__rt__bench_measure_case")
            .unwrap_or_else(|| {
                self.module.add_function(
                    "__rt__bench_measure_case",
                    function_type,
                    Some(Linkage::External),
                )
            })
    }

    fn emit_bench_wrapper(
        &self,
        benchmark_fn: FunctionValue<'llvm>,
        benchmark_abi: &abi::FnAbi<'gcx>,
        finish_rootless_fn: FunctionValue<'llvm>,
        index: usize,
    ) -> PointerValue<'llvm> {
        assert!(
            matches!(benchmark_abi.ret.mode, abi::PassMode::Ignore),
            "@bench functions must return void"
        );
        assert!(
            matches!(benchmark_abi.args.as_slice(), [arg] if matches!(arg.mode, abi::PassMode::Direct)),
            "@bench functions must take one direct &Benchmark argument"
        );

        let wrapper_type = self.context.void_type().fn_type(&[], false);
        let wrapper = self.module.add_function(
            &format!("__taro_bench_wrapper_{index}"),
            wrapper_type,
            Some(Linkage::Private),
        );
        let builder = self.context.create_builder();
        let entry = self.context.append_basic_block(wrapper, "entry");
        builder.position_at_end(entry);

        let TyKind::Reference(benchmark_ty) = benchmark_abi.args[0].ty.kind() else {
            panic!("validated @bench argument must be a mutable reference");
        };
        let benchmark_ty = self
            .lower_ty(benchmark_ty)
            .expect("Benchmark language item must have a runtime representation");
        // Derive storage from the canonical std type itself. This lets std
        // evolve private fast-path fields without duplicating their layout in
        // either codegen or the Rust runtime.
        let argument = builder
            .build_alloca(benchmark_ty, "benchmark_argument")
            .unwrap();
        builder
            .build_store(argument, benchmark_ty.const_zero())
            .unwrap();
        // Benchmark holds no managed values, so an untraced frame slot is a
        // valid GC reference target.
        let reference = { argument.into() };
        builder.build_call(benchmark_fn, &[reference], "").unwrap();
        builder
            .build_call(finish_rootless_fn, &[], "finish_rootless")
            .unwrap();
        builder.build_return(None).unwrap();
        wrapper.as_global_value().as_pointer_value()
    }

    fn build_global_ptr_array(
        &self,
        values: &[PointerValue<'llvm>],
        name: &str,
    ) -> PointerValue<'llvm> {
        let ptr_ty = self.context.ptr_type(AddressSpace::default());
        let arr_ty = ptr_ty.array_type(values.len() as u32);
        let global = self.module.add_global(arr_ty, None, name);
        global.set_initializer(&ptr_ty.const_array(values));
        global.set_constant(true);
        global.set_linkage(Linkage::Private);
        global.set_unnamed_addr(true);
        global.as_pointer_value()
    }

    fn build_global_i8_array(&self, values: &[u8], name: &str) -> PointerValue<'llvm> {
        let i8_ty = self.context.i8_type();
        let arr_ty = i8_ty.array_type(values.len() as u32);
        let vals: Vec<_> = values
            .iter()
            .map(|v| i8_ty.const_int(*v as u64, false))
            .collect();
        let global = self.module.add_global(arr_ty, None, name);
        global.set_initializer(&i8_ty.const_array(&vals));
        global.set_constant(true);
        global.set_linkage(Linkage::Private);
        global.set_unnamed_addr(true);
        global.as_pointer_value()
    }

    fn build_global_usize_array(&self, values: &[u64], name: &str) -> PointerValue<'llvm> {
        let arr_ty = self.usize_ty.array_type(values.len() as u32);
        let vals: Vec<_> = values
            .iter()
            .map(|value| self.usize_ty.const_int(*value, false))
            .collect();
        let global = self.module.add_global(arr_ty, None, name);
        global.set_initializer(&self.usize_ty.const_array(&vals));
        global.set_constant(true);
        global.set_linkage(Linkage::Private);
        global.set_unnamed_addr(true);
        global.as_pointer_value()
    }

    /// Helper: Increment an i32 counter via load-add-store
    fn increment_counter(
        &self,
        builder: &Builder<'llvm>,
        counter_ptr: PointerValue<'llvm>,
        i32_ty: IntType<'llvm>,
    ) {
        let cur = builder
            .build_load(i32_ty, counter_ptr, "cnt")
            .unwrap()
            .into_int_value();
        let inc = builder
            .build_int_add(cur, i32_ty.const_int(1, false), "inc")
            .unwrap();
        builder.build_store(counter_ptr, inc).unwrap();
    }

    /// Helper: declare C puts
    fn declare_puts_fn(&self) -> FunctionValue<'llvm> {
        let ptr_ty = self.context.ptr_type(AddressSpace::default());
        let ty = self.context.i32_type().fn_type(&[ptr_ty.into()], false);
        self.module.get_function("puts").unwrap_or_else(|| {
            self.module
                .add_function("puts", ty, Some(Linkage::External))
        })
    }

    /// Helper: declare C printf (variadic)
    fn declare_printf_fn(&self) -> FunctionValue<'llvm> {
        let ptr_ty = self.context.ptr_type(AddressSpace::default());
        let ty = self.context.i32_type().fn_type(&[ptr_ty.into()], true);
        self.module.get_function("printf").unwrap_or_else(|| {
            self.module
                .add_function("printf", ty, Some(Linkage::External))
        })
    }

    /// Helper: declare
    /// `__rt__test_panic_status(i1, i1, ptr, usize) -> i8`.
    fn declare_test_panic_status_fn(&self) -> FunctionValue<'llvm> {
        let ptr = self.context.ptr_type(AddressSpace::default());
        let i1 = self.context.bool_type();
        let i8 = self.context.i8_type();
        let fn_ty = i8.fn_type(
            &[i1.into(), i1.into(), ptr.into(), self.usize_ty.into()],
            false,
        );
        self.module
            .get_function("__rt__test_panic_status")
            .unwrap_or_else(|| {
                self.module
                    .add_function("__rt__test_panic_status", fn_ty, Some(Linkage::External))
            })
    }

    /// Helper: declare `__rt__test_panic_finish(i8, ptr, usize) -> void`.
    fn declare_test_panic_finish_fn(&self) -> FunctionValue<'llvm> {
        let ptr = self.context.ptr_type(AddressSpace::default());
        let i8 = self.context.i8_type();
        let fn_ty = self
            .context
            .void_type()
            .fn_type(&[i8.into(), ptr.into(), self.usize_ty.into()], false);
        self.module
            .get_function("__rt__test_panic_finish")
            .unwrap_or_else(|| {
                self.module
                    .add_function("__rt__test_panic_finish", fn_ty, Some(Linkage::External))
            })
    }

    /// Helper: declare `__rt__test_call_fn(fn_ptr: ptr) -> i1`
    ///
    /// Sets `IN_TEST_HARNESS`, wraps the call in `catch_unwind`, and returns
    /// `true` if the function panicked.  The `fn_ptr` is typed as an opaque
    /// pointer because LLVM does not care about the callee ABI here — the
    /// runtime casts it internally.
    fn declare_test_call_fn(&self) -> FunctionValue<'llvm> {
        let ptr = self.context.ptr_type(AddressSpace::default());
        let i1 = self.context.bool_type();
        let fn_ty = i1.fn_type(&[ptr.into()], false);
        self.module
            .get_function("__rt__test_call_fn")
            .unwrap_or_else(|| {
                self.module
                    .add_function("__rt__test_call_fn", fn_ty, Some(Linkage::External))
            })
    }

    fn declare_test_prepare_result_fn(&self) -> FunctionValue<'llvm> {
        let ptr = self.context.ptr_type(AddressSpace::default());
        let fn_ty = self.context.void_type().fn_type(&[ptr.into()], false);
        self.module
            .get_function("__rt__test_prepare_result")
            .unwrap_or_else(|| {
                self.module.add_function(
                    "__rt__test_prepare_result",
                    fn_ty,
                    Some(Linkage::External),
                )
            })
    }

    fn declare_fuzz_run_fn(&self) -> FunctionValue<'llvm> {
        let ptr = self.context.ptr_type(AddressSpace::default());
        let i32_ty = self.context.i32_type();
        let fn_ty = i32_ty.fn_type(&[ptr.into(), self.usize_ty.into(), ptr.into()], false);
        self.module
            .get_function("__rt__fuzz_run")
            .unwrap_or_else(|| {
                self.module
                    .add_function("__rt__fuzz_run", fn_ty, Some(Linkage::External))
            })
    }

    fn emit_fuzz_harness(&mut self, target: &crate::compile::fuzz_collector::FuzzTarget) {
        let i32_ty = self.context.i32_type();
        let ptr_ty = self.context.ptr_type(AddressSpace::default());

        let target_instance = Instance::item(target.id, GenericArguments::empty());
        let Some((target_fn, target_fn_abi)) = self.functions.get(&target_instance).cloned() else {
            self.gcx.dcx().emit_error(
                format!(
                    "internal error: fuzz target `{}` was not lowered",
                    target.display_name
                ),
                None,
            );
            return;
        };

        let finish_rootless_fn = self.declare_executor_finish_rootless_fn();
        let wrapper_ty = self
            .context
            .void_type()
            .fn_type(&[ptr_ty.into(), self.usize_ty.into()], false);
        let wrapper = self
            .module
            .add_function("__taro_fuzz_wrapper", wrapper_ty, Some(Linkage::Private));
        let wrapper_builder = self.context.create_builder();
        let wrapper_bb = self.context.append_basic_block(wrapper, "entry");
        wrapper_builder.position_at_end(wrapper_bb);

        let data_ptr = wrapper.get_nth_param(0).unwrap().into_pointer_value();
        let data_len = wrapper.get_nth_param(1).unwrap().into_int_value();
        let span_ty = self
            .context
            .struct_type(&[ptr_ty.into(), self.usize_ty.into()], false);
        let mut span_val = span_ty.get_undef();
        span_val = wrapper_builder
            .build_insert_value(span_val, data_ptr, 0, "fuzz_span_ptr")
            .unwrap()
            .into_struct_value();
        span_val = wrapper_builder
            .build_insert_value(span_val, data_len, 1, "fuzz_span_len")
            .unwrap()
            .into_struct_value();

        let param_mode = target_fn_abi
            .args
            .first()
            .map(|arg| arg.mode)
            .unwrap_or(abi::PassMode::Direct);
        let call_arg: BasicMetadataValueEnum<'llvm> = match param_mode {
            abi::PassMode::Indirect { .. } => {
                let slot = wrapper_builder
                    .build_alloca(span_ty, "fuzz_span_slot")
                    .unwrap();
                wrapper_builder.build_store(slot, span_val).unwrap();
                slot.into()
            }
            abi::PassMode::Direct | abi::PassMode::Ignore => span_val.into(),
        };

        wrapper_builder
            .build_call(target_fn, &[call_arg], "fuzz_target_call")
            .unwrap();
        wrapper_builder
            .build_call(finish_rootless_fn, &[], "fuzz_finish_rootless")
            .unwrap();
        wrapper_builder.build_return(None).unwrap();

        let start_ty = i32_ty.fn_type(&[], false);
        let start_fn = self.module.add_function("taro_start", start_ty, None);
        let builder = self.context.create_builder();
        let entry_bb = self.context.append_basic_block(start_fn, "entry");
        builder.position_at_end(entry_bb);

        let install_stack_guard_fn = self.declare_install_stack_guard_fn();
        builder
            .build_call(install_stack_guard_fn, &[], "install_stack_guard")
            .unwrap();

        let name_ptr = self.build_global_cstring(&target.display_name, "fuzz_target_name");
        let name_len = self
            .usize_ty
            .const_int(target.display_name.len() as u64, false);
        let fuzz_run_fn = self.declare_fuzz_run_fn();
        let exit_code = builder
            .build_call(
                fuzz_run_fn,
                &[
                    name_ptr.into(),
                    name_len.into(),
                    wrapper.as_global_value().as_pointer_value().into(),
                ],
                "fuzz_exit_code",
            )
            .unwrap()
            .try_as_basic_value()
            .basic()
            .unwrap()
            .into_int_value();
        builder.build_return(Some(&exit_code)).unwrap();

        let main_ty = i32_ty.fn_type(&[i32_ty.into(), ptr_ty.into()], false);
        let main_fn = self.module.add_function("main", main_ty, None);
        let main_bb = self.context.append_basic_block(main_fn, "entry");
        let mb = self.context.create_builder();
        mb.position_at_end(main_bb);
        let argc = main_fn
            .get_nth_param(0)
            .expect("main argc parameter missing")
            .into_int_value();
        let argv = main_fn
            .get_nth_param(1)
            .expect("main argv parameter missing")
            .into_pointer_value();
        self.get_or_create_env_argc_global();
        self.get_or_create_env_argv_global();
        self.store_process_args_from_main(&mb, argc, argv);
        let ret = mb
            .build_call(start_fn, &[], "ret")
            .unwrap()
            .try_as_basic_value()
            .basic()
            .map(|v| v.into_int_value())
            .unwrap_or_else(|| i32_ty.const_int(0, false));
        mb.build_return(Some(&ret)).unwrap();
    }

    fn declare_async_run_root_fn(&self) -> FunctionValue<'llvm> {
        let ptr = self.context.ptr_type(AddressSpace::default());
        let fn_ty = self
            .context
            .void_type()
            .fn_type(&[ptr.into(), ptr.into()], false);
        self.module
            .get_function("__rt__async_run_root")
            .unwrap_or_else(|| {
                self.module
                    .add_function("__rt__async_run_root", fn_ty, Some(Linkage::External))
            })
    }

    /// Installs the stack-exhaustion handler.
    ///
    /// Called first thing in every entry shim: without it a thread that runs out
    /// of stack dies on the guard page with no diagnostic at all.
    fn declare_install_stack_guard_fn(&self) -> FunctionValue<'llvm> {
        let fn_ty = self.context.void_type().fn_type(&[], false);
        self.module
            .get_function("__rt__install_stack_guard")
            .unwrap_or_else(|| {
                self.module.add_function(
                    "__rt__install_stack_guard",
                    fn_ty,
                    Some(Linkage::External),
                )
            })
    }

    fn declare_executor_finish_rootless_fn(&self) -> FunctionValue<'llvm> {
        let fn_ty = self.context.void_type().fn_type(&[], false);
        self.module
            .get_function("__rt__executor_finish_rootless")
            .unwrap_or_else(|| {
                self.module.add_function(
                    "__rt__executor_finish_rootless",
                    fn_ty,
                    Some(Linkage::External),
                )
            })
    }

    fn declare_executor_finish_main_fn(&self) -> FunctionValue<'llvm> {
        let fn_ty = self.context.void_type().fn_type(&[], false);
        self.module
            .get_function("__rt__executor_finish_main")
            .unwrap_or_else(|| {
                self.module.add_function(
                    "__rt__executor_finish_main",
                    fn_ty,
                    Some(Linkage::External),
                )
            })
    }

    fn declare_executor_abort_rootless_fn(&self) -> FunctionValue<'llvm> {
        let fn_ty = self.context.void_type().fn_type(&[], false);
        self.module
            .get_function("__rt__executor_abort_rootless")
            .unwrap_or_else(|| {
                self.module.add_function(
                    "__rt__executor_abort_rootless",
                    fn_ty,
                    Some(Linkage::External),
                )
            })
    }

    fn emit_sync_test_wrapper(
        &self,
        sync_test_fn: FunctionValue<'llvm>,
        sync_test_abi: &abi::FnAbi<'gcx>,
        finish_rootless_fn: FunctionValue<'llvm>,
        index: usize,
    ) -> PointerValue<'llvm> {
        self.assert_entry_abi_takes_no_args(sync_test_abi, "sync `@test` function");
        let wrapper_ty = self.context.void_type().fn_type(&[], false);
        let wrapper = self.module.add_function(
            &format!("__taro_sync_test_wrapper_{index}"),
            wrapper_ty,
            Some(Linkage::Private),
        );
        let builder = self.context.create_builder();
        let entry = self.context.append_basic_block(wrapper, "entry");
        builder.position_at_end(entry);

        builder.build_call(sync_test_fn, &[], "").unwrap();
        builder
            .build_call(finish_rootless_fn, &[], "finish_rootless")
            .unwrap();
        builder.build_return(None).unwrap();
        wrapper.as_global_value().as_pointer_value()
    }

    fn emit_async_test_wrapper(
        &self,
        async_test_fn: FunctionValue<'llvm>,
        async_test_abi: &abi::FnAbi<'gcx>,
        async_run_root_fn: FunctionValue<'llvm>,
        index: usize,
    ) -> PointerValue<'llvm> {
        // The async entry returns a runtime handle pointer, which is always
        // scalar-sized; an indirect return here would mean the ABI no longer
        // matches the handle-based protocol this wrapper is built around.
        self.assert_entry_abi_takes_no_args(async_test_abi, "async `@test` function");
        let wrapper_ty = self.context.void_type().fn_type(&[], false);
        let wrapper = self.module.add_function(
            &format!("__taro_async_test_wrapper_{index}"),
            wrapper_ty,
            Some(Linkage::Private),
        );
        let builder = self.context.create_builder();
        let entry = self.context.append_basic_block(wrapper, "entry");
        builder.position_at_end(entry);

        let handle = builder
            .build_call(async_test_fn, &[], "async_test_handle")
            .unwrap()
            .try_as_basic_value()
            .basic()
            .expect("async test constructor should return a runtime handle")
            .into_pointer_value();
        let dummy = builder
            .build_alloca(self.context.i8_type(), "async_test_dummy")
            .unwrap();
        builder
            .build_call(
                async_run_root_fn,
                &[handle.into(), dummy.as_basic_value_enum().into()],
                "",
            )
            .unwrap();
        builder.build_return(None).unwrap();
        wrapper.as_global_value().as_pointer_value()
    }

    /// Helper: create a null-terminated global string constant, return pointer
    fn build_global_cstring(&self, value: &str, name: &str) -> PointerValue<'llvm> {
        let bytes: Vec<u8> = value.bytes().chain(std::iter::once(0)).collect();
        let vals: Vec<_> = bytes
            .iter()
            .map(|b| self.context.i8_type().const_int(*b as u64, false))
            .collect();
        let arr_ty = self.context.i8_type().array_type(bytes.len() as u32);
        let global = self.module.add_global(arr_ty, None, name);
        global.set_initializer(&self.context.i8_type().const_array(&vals));
        global.set_constant(true);
        global.set_linkage(Linkage::Private);
        global.set_unnamed_addr(true);
        global.as_pointer_value()
    }

    fn get_panic_abort_unwind_fn(&self) -> FunctionValue<'llvm> {
        let ptr_ty = self.context.ptr_type(AddressSpace::default());
        let fn_ty = self.context.void_type().fn_type(&[ptr_ty.into()], false);
        self.module
            .get_function("__rt__panic_abort_unwind")
            .unwrap_or_else(|| {
                self.module
                    .add_function("__rt__panic_abort_unwind", fn_ty, Some(Linkage::External))
            })
    }

    fn get_panic_unwind_at_fn(&mut self) -> FunctionValue<'llvm> {
        let str_ty = string_header_ty(self.context, &self.target_data);
        let fn_ty = self.context.void_type().fn_type(
            &[
                str_ty.into(),
                str_ty.into(),
                self.usize_ty.into(),
                self.usize_ty.into(),
            ],
            false,
        );
        self.get_or_add_external_function("__rt__panic_unwind_at", fn_ty)
    }

    fn const_string_value(&mut self, value: &str) -> BasicValueEnum<'llvm> {
        let sym = self.gcx.intern_symbol(value);
        let ptr = self.lower_string(sym);
        let len = self.usize_ty.const_int(value.len() as u64, false);
        let string_ty = string_header_ty(self.context, &self.target_data);
        self.string_constant_header(string_ty, ptr, len)
            .as_basic_value_enum()
    }

    fn std_panic_kind_for_call(&self, func: &Operand<'gcx>) -> Option<StdPanicCallKind> {
        let Operand::Constant(c) = func else {
            return None;
        };
        let mir::ConstantKind::Function(def_id, _, _) = c.value else {
            return None;
        };
        let Some(std_pkg) = self.gcx.std_package_index() else {
            return None;
        };
        if def_id.package() != std_pkg {
            return None;
        }
        let ident = self.gcx.definition_ident(def_id);
        let Some(parent) = self.gcx.definition_parent(def_id) else {
            return None;
        };
        if !self
            .gcx
            .symbol_eq(self.gcx.definition_ident(parent).symbol, "panic")
        {
            return None;
        }
        match self.gcx.symbol_text(ident.symbol).as_str() {
            "panic" => Some(StdPanicCallKind::Panic),
            "todo" => Some(StdPanicCallKind::Todo),
            "unreachable" => Some(StdPanicCallKind::Unreachable),
            _ => None,
        }
    }

    fn try_lower_std_panic_call(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        span: crate::span::Span,
        func: &Operand<'gcx>,
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
        normal_bb: BasicBlock<'llvm>,
        unwind_target: Option<BasicBlock<'llvm>>,
    ) -> CompileResult<bool> {
        let Some(kind) = self.std_panic_kind_for_call(func) else {
            return Ok(false);
        };

        let mut lowered_args: Vec<BasicValueEnum<'llvm>> = match kind {
            StdPanicCallKind::Panic | StdPanicCallKind::Todo => {
                let lowered = self.lower_call_args(body, locals, args)?;
                if lowered.len() != 1 {
                    self.gcx.dcx().emit_error(
                        format!(
                            "std panic call expected one message argument, got {}",
                            lowered.len()
                        ),
                        Some(span),
                    );
                    return Err(crate::error::ReportedError);
                }
                lowered
            }
            StdPanicCallKind::Unreachable => {
                vec![self.const_string_value("entered unreachable code")]
            }
        };

        let file = self
            .gcx
            .dcx()
            .file_path(span.file)
            .map(|p| p.to_string_lossy().into_owned())
            .unwrap_or_else(|| "<unknown>".to_string());
        let line = (span.start.line + 1) as u64;
        let column = (span.start.offset + 1) as u64;

        lowered_args.push(self.const_string_value(&file));
        lowered_args.push(self.usize_ty.const_int(line, false).as_basic_value_enum());
        lowered_args.push(self.usize_ty.const_int(column, false).as_basic_value_enum());

        self.emit_source_typed_gc_stack_map(span, StackMapSiteKind::Panic);
        let panic_fn = self.get_panic_unwind_at_fn();
        let call_site = self.emit_call_maybe_unwind(
            CallTarget::Direct(panic_fn),
            &lowered_args,
            unwind_target,
            "panic_unwind_at",
        )?;
        if let Some(ret) = call_site.try_as_basic_value().basic() {
            self.store_place(destination, body, locals, ret)?;
        }
        let _ = self.builder.build_unconditional_branch(normal_bb).unwrap();
        Ok(true)
    }

    fn run_optimization_passes(&self) -> CompileResult<()> {
        // Honor always-inline declarations before the selected optimization pipeline.
        self.module
            .run_passes(
                "always-inline",
                &self.target_machine,
                PassBuilderOptions::create(),
            )
            .map_err(|error| {
                self.gcx.dcx().emit_error(
                    format!("LLVM runtime fast-path expansion failed: {error}"),
                    None,
                );
                crate::error::ReportedError
            })?;
        let pipeline = llvm_optimization_pipeline(
            self.gcx.config.profile,
            self.gcx.config.codegen.optimization,
            self.gcx.config.codegen.lto,
        );

        match pipeline {
            LlvmOptimizationPipeline::Function(pipeline) => {
                // Baseline and O0 intentionally retain the old function-level
                // scope. Declarations have no body for LLVMRunPassesOnFunction.
                for function in self.module.get_functions() {
                    if !has_llvm_function_body(function) {
                        continue;
                    }
                    let name = function.get_name().to_string_lossy();
                    let options = PassBuilderOptions::create();
                    options.set_verify_each(cfg!(test));
                    if let Err(error) = function.run_passes(pipeline, &self.target_machine, options)
                    {
                        self.gcx.dcx().emit_error(
                            format!(
                                "LLVM function pass pipeline `{pipeline}` failed for `{name}`: {error}"
                            ),
                            None,
                        );
                        return Err(crate::error::ReportedError);
                    }
                }
            }
            LlvmOptimizationPipeline::Module(pipeline) => {
                let options = PassBuilderOptions::create();
                options.set_verify_each(cfg!(test));
                if let Err(error) = self
                    .module
                    .run_passes(pipeline, &self.target_machine, options)
                {
                    self.gcx.dcx().emit_error(
                        format!("LLVM module pass pipeline `{pipeline}` failed: {error}"),
                        None,
                    );
                    return Err(crate::error::ReportedError);
                }
            }
        }

        Ok(())
    }

    fn emit_module_artifact(&mut self) -> CompileResult<ModuleArtifact> {
        let out_dir = self.gcx.output_root().clone();
        if let Err(e) = fs::create_dir_all(&out_dir) {
            let msg = format!("failed to create output directory: {e}");
            self.gcx.dcx().emit_error(msg.into(), None);
            return Err(crate::error::ReportedError);
        }
        let kind = self.gcx.config.codegen.artifact;
        let path = out_dir.join(format!(
            "{}.{}",
            self.gcx.config.identifier,
            kind.extension()
        ));
        let descriptors_path = out_dir.join(format!("{}.stackmaps", self.gcx.config.identifier));
        let target_triple = self
            .gcx
            .store
            .target_layout
            .triple()
            .as_str()
            .to_string_lossy()
            .into_owned();
        let descriptor_result = {
            crate::codegen::gc_stack_maps::write_pending_module(
                &descriptors_path,
                &crate::codegen::gc_stack_maps::PendingStackMapModule::new(
                    target_triple.clone(),
                    self.pending_gc_stack_maps.clone(),
                ),
            )
        };
        descriptor_result.map_err(|message| {
            self.gcx.dcx().emit_error(message, None);
            crate::error::ReportedError
        })?;

        let pc_metadata = match kind {
            ModuleArtifactKind::Object => {
                self.target_machine
                    .write_to_file(&self.module, FileType::Object, &path)
                    .map_err(|error| {
                        self.gcx
                            .dcx()
                            .emit_error(format!("failed to write object file: {error}"), None);
                        crate::error::ReportedError
                    })?;
                let metadata_path =
                    out_dir.join(format!("{}.pcmeta.o", self.gcx.config.identifier));
                {
                    let metadata = crate::codegen::gc_stack_maps::normalize_object(
                        &path,
                        [descriptors_path.clone()],
                        &target_triple,
                    )
                    .map_err(|message| {
                        self.gcx.dcx().emit_error(
                            format!("failed to normalize GC root metadata: {message}"),
                            None,
                        );
                        crate::error::ReportedError
                    })?;
                    #[cfg(test)]
                    let metadata = {
                        let mut metadata = metadata;
                        if let Some(hook) = self.gc_metadata_test_hook {
                            hook(&mut metadata);
                        }
                        metadata
                    };
                    crate::codegen::gc_pc_metadata::emit_object(
                        &metadata,
                        &self.target_machine,
                        &metadata_path,
                    )
                    .map_err(|message| {
                        self.gcx.dcx().emit_error(message, None);
                        crate::error::ReportedError
                    })?;
                }
                strip_object(&path).map_err(|message| {
                    self.gcx.dcx().emit_error(message, None);
                    crate::error::ReportedError
                })?;
                Some(metadata_path)
            }
            ModuleArtifactKind::LlvmBitcode => {
                // Inkwell's path-based bitcode writer requires Unicode and
                // panics for other paths. Writing LLVM's memory buffer through
                // std::fs keeps valid platform paths diagnostic-safe.
                let written = if self.gcx.config.codegen.lto == LtoMode::Thin {
                    crate::codegen::lto::write_thin_lto_bitcode(&self.module, &path)
                } else {
                    write_llvm_bitcode(&self.module, &path).map_err(|error| error.to_string())
                };
                written.map_err(|error| {
                    self.gcx
                        .dcx()
                        .emit_error(format!("failed to write LLVM bitcode: {error}"), None);
                    crate::error::ReportedError
                })?;
                None
            }
        };

        Ok(ModuleArtifact::new(kind, path).with_stack_maps(descriptors_path, pc_metadata))
    }

    fn lower_body(
        &mut self,
        instance: Instance<'gcx>,
        body: &'gcx mir::Body<'gcx>,
    ) -> CompileResult<()> {
        let finalized = { self.gcx.is_finalized_gc_instance_mir(instance, body) };
        if !finalized {
            self.gcx.dcx().emit_error(
                format!(
                    "codegen received non-finalized MIR for `{}`",
                    mangle_instance(self.gcx, instance)
                ),
                Some(self.gcx.definition_ident(instance.def_id()).span),
            );
            return Err(crate::error::ReportedError);
        }

        // Set substitution context for monomorphization
        self.current_subst = instance.args();

        let (function, fn_abi) = self
            .functions
            .get(&instance)
            .cloned()
            .expect("function must be declared");
        self.current_fn = Some(function);
        self.current_fn_abi = Some(fn_abi.clone());
        self.current_body = Some(body);
        self.current_mir_location = None;
        self.current_stack_map_ordinal = 0;
        if let Some(debug) = &mut self.debug {
            debug.begin_function(function, body, self.gcx);
        }
        self.current_sret_ptr = if matches!(fn_abi.ret.mode, abi::PassMode::Indirect { .. }) {
            function
                .get_nth_param(0)
                .map(|param| param.into_pointer_value())
        } else {
            None
        };

        // Create a preamble block for allocas before branching into the MIR
        // entry block.
        let preamble_block = self.context.append_basic_block(function, "preamble");
        let llvm_blocks = self.create_blocks(function, body);
        let mir_entry_block = llvm_blocks[body.start_block.index()];
        if self.body_has_unwind(body) {
            function.set_personality_function(self.eh_personality_fn());
            self.eh_slot = Some(self.allocate_eh_slot(preamble_block));
        } else {
            self.eh_slot = None;
        }
        let mut locals = self.allocate_locals(body, preamble_block, function, &fn_abi);
        self.builder.position_at_end(preamble_block);
        // Every GC function records a source PC selector for its safepoints.
        self.current_stack_map_selector = Some({
            let selector = self
                .builder
                .build_alloca(self.context.i64_type(), "source_pc_selector")
                .expect("allocate safepoint selector");
            let initialize = self
                .builder
                .build_store(selector, self.context.i64_type().const_zero())
                .expect("initialize safepoint selector");
            initialize
                .set_volatile(true)
                .expect("safepoint selector initialization must be volatile");
            selector
        });
        let mut gc_frame = self.gc_frame(body, &locals)?;
        self.publish_address_holders(instance, body, &mut gc_frame)?;
        self.current_gc_frame = Some(gc_frame);
        self.builder
            .build_unconditional_branch(mir_entry_block)
            .unwrap();

        let fn_coverage = self.coverage.as_mut().and_then(|cov| {
            cov.prepare_function(
                instance,
                function,
                body,
                self.context,
                &self.module,
                self.gcx,
            )
        });

        for (bb_id, bb) in body.basic_blocks.iter_enumerated() {
            let llvm_bb = llvm_blocks[bb_id.index()];
            self.builder.position_at_end(llvm_bb);
            self.current_source_scope = mir::SourceScopeId::from_raw(0);
            if let Some(cov) = &fn_coverage {
                self.unset_debug_location();
                cov.emit_block_counter(bb_id, self.context, &self.module, &self.builder);
            }

            for (statement_index, stmt) in bb.statements.iter().enumerate() {
                self.current_mir_location = Some(mir::analysis::liveness::MirLocation::Statement {
                    block: bb_id,
                    index: statement_index,
                });
                self.current_span = Some(stmt.span);
                self.set_debug_location(stmt.span);
                self.lower_statement(body, &mut locals, stmt)?;
            }

            if let Some(term) = &bb.terminator {
                self.current_mir_location =
                    Some(mir::analysis::liveness::MirLocation::Terminator { block: bb_id });
                self.current_span = Some(term.span);
                self.set_debug_location(term.span);
                self.lower_terminator(body, &mut locals, term, &llvm_blocks)?;
            } else if llvm_bb.get_terminator().is_none() {
                self.unset_debug_location();
                let _ = self.builder.build_unreachable().unwrap();
            }
        }

        if let Some(debug) = &mut self.debug {
            debug.end_function(&self.builder);
        }
        // Explicit map operands are complete only before LLVM inlining. MIR is
        // Taro's map-aware inliner; collecting LLVM functions must keep their
        // physical frame against both inlining and tail-call elimination, and
        // remain unwindable through rootless sites, so caller roots cannot be lost.
        self.preserve_diagnostic_frame(function);
        self.eh_slot = None;
        self.current_fn = None;
        self.current_fn_abi = None;
        self.current_sret_ptr = None;
        self.current_body = None;
        self.current_mir_location = None;
        self.current_span = None;
        self.current_stack_map_selector = None;
        self.current_gc_frame = None;
        Ok(())
    }

    fn set_debug_location(&mut self, span: crate::span::Span) {
        if let Some(debug) = &mut self.debug {
            debug.set_location(self.context, &self.builder, self.gcx, span);
        }
    }

    fn unset_debug_location(&self) {
        if self.debug.is_some() {
            self.builder.unset_current_debug_location();
        }
    }

    fn finalize_debug_info(&self) {
        if let Some(debug) = &self.debug {
            debug.finalize();
        }
    }

    fn finalize_coverage(&self) -> CompileResult<()> {
        if let Some(coverage) = &self.coverage {
            coverage.finalize(self.context, &self.module, &self.target_machine, self.gcx)?;
        }
        Ok(())
    }

    fn body_has_unwind(&self, body: &mir::Body<'gcx>) -> bool {
        body.basic_blocks.iter().any(|bb| {
            bb.terminator.as_ref().is_some_and(|term| match term.kind {
                mir::TerminatorKind::ResumeUnwind => true,
                mir::TerminatorKind::Call {
                    unwind: mir::CallUnwindAction::Cleanup(_),
                    ..
                } => true,
                _ => false,
            })
        })
    }

    fn call_effect(
        &self,
        func: &mir::Operand<'gcx>,
    ) -> crate::error::CompileResult<mir::CallEffect> {
        mir::analysis::effects::classify_call_effect(self.gcx, func).map_err(|message| {
            self.gcx.dcx().emit_error(message, self.current_span);
            crate::error::ReportedError
        })
    }

    fn eh_personality_fn(&mut self) -> FunctionValue<'llvm> {
        if let Some(personality) = self.eh_personality {
            return personality;
        }
        let ty = self.context.i32_type().fn_type(&[], true);
        let func = self
            .module
            .get_function("__gcc_personality_v0")
            .unwrap_or_else(|| {
                self.module
                    .add_function("__gcc_personality_v0", ty, Some(Linkage::External))
            });
        self.eh_personality = Some(func);
        func
    }

    fn eh_landingpad_ty(&self) -> StructType<'llvm> {
        let ptr = self.context.ptr_type(AddressSpace::default());
        self.context
            .struct_type(&[ptr.into(), self.context.i32_type().into()], false)
    }

    fn allocate_eh_slot(
        &self,
        entry_block: inkwell::basic_block::BasicBlock<'llvm>,
    ) -> PointerValue<'llvm> {
        let alloc_builder = self.context.create_builder();
        alloc_builder.position_at_end(entry_block);
        alloc_builder
            .build_alloca(self.eh_landingpad_ty(), "eh_slot")
            .unwrap()
    }

    /// Build an alloca in the entry block of the function currently being
    /// emitted. Temporaries must not be allocated at the builder's insertion
    /// point: an alloca there executes every time control reaches it, so a
    /// hot loop would grow the stack each iteration, released only at
    /// function return.
    fn build_entry_alloca<T: BasicType<'llvm>>(&self, ty: T, name: &str) -> PointerValue<'llvm> {
        let entry = self
            .builder
            .get_insert_block()
            .and_then(|bb| bb.get_parent())
            .and_then(|func| func.get_first_basic_block())
            .expect("builder must be positioned inside a function");
        let alloc_builder = self.context.create_builder();
        match entry.get_terminator() {
            Some(terminator) => alloc_builder.position_before(&terminator),
            None => alloc_builder.position_at_end(entry),
        }
        alloc_builder.build_alloca(ty, name).unwrap()
    }

    fn append_block_to_current_fn(&self, name: &str) -> inkwell::basic_block::BasicBlock<'llvm> {
        let function = self.current_fn.expect("current function must be set");
        self.context.append_basic_block(function, name)
    }

    fn emit_cleanup_landingpad(
        &mut self,
        unwind_target: inkwell::basic_block::BasicBlock<'llvm>,
    ) -> CompileResult<()> {
        let personality = self.eh_personality_fn();
        let landing = self
            .builder
            .build_landing_pad(self.eh_landingpad_ty(), personality, &[], true, "lpad")
            .unwrap();
        let Some(eh_slot) = self.eh_slot else {
            self.gcx
                .dcx()
                .emit_error("missing EH slot for unwind path".into(), None);
            return Err(crate::error::ReportedError);
        };
        let _ = self.builder.build_store(eh_slot, landing).unwrap();
        let _ = self
            .builder
            .build_unconditional_branch(unwind_target)
            .unwrap();
        Ok(())
    }

    fn lower_call_args(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &[LocalStorage<'llvm>],
        args: &[Operand<'gcx>],
    ) -> CompileResult<Vec<BasicValueEnum<'llvm>>> {
        let mut lowered = Vec::with_capacity(args.len());
        for arg in args {
            if let Some(val) = self.eval_operand(body, locals, arg)? {
                lowered.push(val);
            }
        }
        Ok(lowered)
    }

    fn lower_indirect_call_arg(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &[LocalStorage<'llvm>],
        arg: &Operand<'gcx>,
        arg_ty: Ty<'gcx>,
    ) -> CompileResult<Option<PointerValue<'llvm>>> {
        if let Operand::Copy(place) | Operand::CopyWith(place, _) = arg {
            if let Some(ptr) = self.place_address(body, locals, place)? {
                return Ok(Some(ptr));
            }
        }

        let Some(value) = self.eval_operand(body, locals, arg)? else {
            return Ok(None);
        };
        let Some(spill_ty) = self.lower_ty(arg_ty) else {
            return Ok(None);
        };
        let spill = self.build_entry_alloca(spill_ty, "indirect_arg");
        let _ = self.builder.build_store(spill, value).unwrap();
        Ok(Some(spill))
    }

    /// Lower an indirectly passed argument by spilling it to a fresh stack
    /// slot. The callee adopts the incoming pointer as the parameter's own
    /// storage (see `allocate_locals`), so forwarding a raw place address
    /// would let the callee mutate the caller's place through it and would
    /// let the sret destination alias an argument (e.g. `x = f(x)`).
    fn lower_indirect_call_arg_copy(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &[LocalStorage<'llvm>],
        arg: &Operand<'gcx>,
        arg_ty: Ty<'gcx>,
    ) -> CompileResult<Option<PointerValue<'llvm>>> {
        let Some(spill_ty) = self.lower_ty(arg_ty) else {
            return Ok(None);
        };

        if let Operand::Copy(place) | Operand::CopyWith(place, _) = arg {
            if let Some(src) = self.place_address(body, locals, place)? {
                let spill = self.build_entry_alloca(spill_ty, "indirect_arg_copy");
                let size = self.target_data.get_store_size(&spill_ty);
                let align = self.target_data.get_abi_alignment(&spill_ty).max(1);
                let count = self.usize_ty.const_int(size, false);
                let _ = self
                    .builder
                    .build_memcpy(spill, align, src, align, count)
                    .unwrap();
                return Ok(Some(spill));
            }
        }

        let Some(value) = self.eval_operand(body, locals, arg)? else {
            return Ok(None);
        };
        let spill = self.build_entry_alloca(spill_ty, "indirect_arg");
        let _ = self.builder.build_store(spill, value).unwrap();
        Ok(Some(spill))
    }

    fn place_address(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &[LocalStorage<'llvm>],
        place: &Place<'gcx>,
    ) -> CompileResult<Option<PointerValue<'llvm>>> {
        if self.lower_ty(self.place_ty(body, place)).is_none() {
            return Ok(None);
        }
        if place.projection.is_empty() {
            return Ok(match locals[place.local.index()] {
                LocalStorage::Stack(ptr) => Some(ptr),
                LocalStorage::Value(_) => None,
            });
        }
        Ok(Some(self.project_place(place, body, locals)?))
    }

    fn lower_call_args_with_fn_abi(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &[LocalStorage<'llvm>],
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
        fn_abi: &abi::FnAbi<'gcx>,
    ) -> CompileResult<Vec<BasicValueEnum<'llvm>>> {
        let mut lowered = Vec::with_capacity(args.len() + 1);
        if matches!(fn_abi.ret.mode, abi::PassMode::Indirect { .. }) {
            let Some(sret_dest) = self.place_address(body, locals, destination)? else {
                self.gcx.dcx().emit_error(
                    "indirect return call requires an addressable destination".into(),
                    None,
                );
                return Err(crate::error::ReportedError);
            };
            lowered.push(sret_dest.as_basic_value_enum());
        }

        for (index, arg) in args.iter().enumerate() {
            let abi_arg = fn_abi.args.get(index);
            let mode = abi_arg.map(|a| a.mode).unwrap_or(abi::PassMode::Direct);
            match mode {
                abi::PassMode::Ignore => {}
                abi::PassMode::Direct => {
                    if let Some(abi_arg) = abi_arg {
                        let expected_ty = self.mono_ty_if_resolved(abi_arg.ty);
                        let actual_ty = self.mono_ty_if_resolved(self.operand_ty(body, arg));
                        let expects_pointer = matches!(
                            expected_ty.kind(),
                            TyKind::Pointer(..) | TyKind::Reference(..)
                        );
                        let actual_is_pointer = matches!(
                            actual_ty.kind(),
                            TyKind::Pointer(..) | TyKind::Reference(..)
                        );

                        // Generic callable lowering can route through trait call shims while
                        // preserving the closure value as the operand
                        // while the concrete closure body expects a pointer receiver. Materialize
                        // an address in that case instead of passing the value bits directly.
                        if expects_pointer && !actual_is_pointer {
                            if let Some(ptr) =
                                self.lower_indirect_call_arg(body, locals, arg, actual_ty)?
                            {
                                lowered.push(
                                    if matches!(expected_ty.kind(), TyKind::Reference(..)) {
                                        self.lexical_reference(ptr)
                                    } else {
                                        ptr.into()
                                    },
                                );
                                continue;
                            }
                        }
                        if !expects_pointer && actual_is_pointer {
                            if let Some(value) = self.eval_operand(body, locals, arg)? {
                                let ptr = self.reference_data(value);
                                if !expected_ty.needs_instantiation()
                                    && let Some(load_ty) = self.lower_ty(expected_ty)
                                {
                                    let loaded = self
                                        .builder
                                        .build_load(load_ty, ptr, "direct_arg")
                                        .unwrap();
                                    lowered.push(loaded);
                                    continue;
                                }
                            }
                        }
                    }
                    if let Some(val) = self.eval_operand(body, locals, arg)? {
                        lowered.push(val);
                    }
                }
                abi::PassMode::Indirect { .. } => {
                    let arg_ty = abi_arg
                        .map(|a| a.ty)
                        .unwrap_or_else(|| self.operand_ty(body, arg));
                    let ptr = self.lower_indirect_call_arg_copy(body, locals, arg, arg_ty)?;
                    if let Some(ptr) = ptr {
                        lowered.push(ptr.as_basic_value_enum());
                    }
                }
            }
        }
        Ok(lowered)
    }

    fn store_call_result(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        destination: &Place<'gcx>,
        fn_abi: &abi::FnAbi<'gcx>,
        call_site: CallSiteValue<'llvm>,
    ) -> CompileResult<()> {
        if matches!(fn_abi.ret.mode, abi::PassMode::Indirect { .. }) {
            return Ok(());
        }
        if let Some(ret) = call_site.try_as_basic_value().basic() {
            self.store_place(destination, body, locals, ret)?;
        }
        Ok(())
    }

    fn emit_call_maybe_unwind(
        &mut self,
        target: CallTarget<'llvm>,
        args: &[BasicValueEnum<'llvm>],
        unwind_target: Option<BasicBlock<'llvm>>,
        name: &str,
    ) -> CompileResult<CallSiteValue<'llvm>> {
        if let Some(unwind_bb) = unwind_target {
            let invoke_normal_bb = self.append_block_to_current_fn("invoke_ok");
            let landing_bb = self.append_block_to_current_fn("invoke_lpad");
            let (fn_ty, fn_ptr) = match target {
                CallTarget::Direct(function) => {
                    let param_types: Vec<BasicMetadataTypeEnum<'llvm>> =
                        args.iter().map(|arg| arg.get_type().into()).collect();
                    let declared_ty = function.get_type();
                    let fn_ty = match declared_ty.get_return_type() {
                        Some(ret) => ret.fn_type(&param_types, declared_ty.is_var_arg()),
                        None => self
                            .context
                            .void_type()
                            .fn_type(&param_types, declared_ty.is_var_arg()),
                    };
                    (fn_ty, function.as_global_value().as_pointer_value())
                }
                CallTarget::Indirect(fn_ty, fn_ptr) => (fn_ty, fn_ptr),
            };
            let call_site = self
                .builder
                .build_indirect_invoke(fn_ty, fn_ptr, args, invoke_normal_bb, landing_bb, name)
                .unwrap();
            self.builder.position_at_end(landing_bb);
            self.emit_cleanup_landingpad(unwind_bb)?;
            self.builder.position_at_end(invoke_normal_bb);
            Ok(call_site)
        } else {
            let args_meta: Vec<BasicMetadataValueEnum<'llvm>> = args
                .iter()
                .copied()
                .map(BasicMetadataValueEnum::from)
                .collect();
            Ok(match target {
                CallTarget::Direct(function) => self.builder.build_call(function, &args_meta, name),
                CallTarget::Indirect(fn_ty, fn_ptr) => self
                    .builder
                    .build_indirect_call(fn_ty, fn_ptr, &args_meta, name),
            }
            .unwrap())
        }
    }

    fn create_blocks(
        &self,
        function: FunctionValue<'llvm>,
        body: &mir::Body<'gcx>,
    ) -> Vec<inkwell::basic_block::BasicBlock<'llvm>> {
        let mut blocks = Vec::with_capacity(body.basic_blocks.len());
        for (idx, _) in body.basic_blocks.iter().enumerate() {
            blocks.push(
                self.context
                    .append_basic_block(function, &format!("bb{idx}")),
            );
        }
        blocks
    }

    fn allocate_locals(
        &self,
        body: &mir::Body<'gcx>,
        entry_block: inkwell::basic_block::BasicBlock<'llvm>,
        function: FunctionValue<'llvm>,
        fn_abi: &abi::FnAbi<'gcx>,
    ) -> Vec<LocalStorage<'llvm>> {
        let alloc_builder = self.context.create_builder();
        alloc_builder.position_at_end(entry_block);
        let indirect_ret_ptr = match fn_abi.ret.mode {
            abi::PassMode::Indirect { .. } => Some(
                function
                    .get_nth_param(0)
                    .expect("sret param")
                    .into_pointer_value(),
            ),
            _ => None,
        };

        let mut locals = Vec::with_capacity(body.locals.len());
        for (idx, decl) in body.locals.iter().enumerate() {
            // For indirect returns, write the MIR return local directly into the hidden
            // sret destination to avoid a giant aggregate load/store at function exit.
            if idx == body.return_local.index() {
                if let Some(sret_ptr) = indirect_ret_ptr {
                    locals.push(LocalStorage::Stack(sret_ptr));
                    continue;
                }
            }
            let name = decl
                .name
                .map(|s| self.gcx.symbol_text(s).to_string())
                .unwrap_or_else(|| format!("tmp{idx}"));

            // Use stack slots for all locals with a representable LLVM type.
            // This avoids incorrect behavior at control-flow joins when "locals"
            // are tracked purely in the emitter (would require PHI construction).
            let storage = match self.lower_ty(decl.ty) {
                Some(ty) => {
                    let slot = alloc_builder.build_alloca(ty, &name).unwrap();
                    LocalStorage::Stack(slot)
                }
                None => LocalStorage::Value(None),
            };
            locals.push(storage);
        }

        // Seed parameters with incoming SSA arguments.
        let mut params = function.get_param_iter();
        if matches!(fn_abi.ret.mode, abi::PassMode::Indirect { .. }) {
            let _ = params.next();
        }
        let param_local_indices: Vec<usize> = body
            .locals
            .iter()
            .enumerate()
            .filter_map(|(idx, decl)| {
                if matches!(decl.kind, mir::LocalKind::Param) {
                    Some(idx)
                } else {
                    None
                }
            })
            .collect();

        for (param_index, local_index) in param_local_indices.into_iter().enumerate() {
            let Some(arg_abi) = fn_abi.args.get(param_index) else {
                continue;
            };

            match arg_abi.mode {
                abi::PassMode::Ignore => {}
                abi::PassMode::Direct => {
                    let Some(arg) = params.next() else {
                        continue;
                    };
                    match locals[local_index] {
                        LocalStorage::Value(_) => {
                            locals[local_index] = LocalStorage::Value(Some(arg));
                        }
                        LocalStorage::Stack(slot) => {
                            let _ = alloc_builder.build_store(slot, arg).unwrap();
                        }
                    }
                }
                abi::PassMode::Indirect { .. } => {
                    let Some(arg) = params.next() else {
                        continue;
                    };
                    // Adopt the incoming pointer as the parameter's storage.
                    // This relies on callers passing a pointer the callee may
                    // treat as its own (a defensive copy or a dead temporary;
                    // see `lower_indirect_call_arg_copy` /
                    // by copying into the parameter slot), so writes to the
                    // parameter never leak back into a caller place.
                    locals[local_index] = LocalStorage::Stack(arg.into_pointer_value());
                }
            }
        }

        locals
    }

    fn logical_frames_for_site(
        &self,
        body: &mir::Body<'gcx>,
        span: crate::span::Span,
    ) -> Vec<PendingLogicalFrame> {
        let mut frames = Vec::new();
        let mut scope = self.current_source_scope;
        let mut location = span;
        loop {
            let data = body
                .source_scopes
                .get(scope)
                .expect("validated MIR source scope");
            let name = self
                .gcx
                .try_definition_ident(data.definition)
                .map(|ident| self.gcx.symbol_text(ident.symbol).to_string())
                .unwrap_or_else(|| {
                    format!(
                        "p{}_d{}",
                        data.definition.package().raw(),
                        data.definition.index().raw()
                    )
                });
            let file = self
                .gcx
                .dcx()
                .file_path(location.file)
                .map(|path| path.to_string_lossy().into_owned())
                .unwrap_or_else(|| "<unknown>".into());
            frames.push(PendingLogicalFrame {
                function: name,
                file,
                line: u32::try_from(location.start.line.saturating_add(1)).unwrap_or(u32::MAX),
                column: u32::try_from(location.start.offset.saturating_add(1)).unwrap_or(u32::MAX),
            });
            let Some(parent) = data.parent else {
                break;
            };
            location = data.callsite.unwrap_or(location);
            scope = parent;
        }
        frames
    }

    fn get_rt_existential_lookup_conformance(&self) -> FunctionValue<'llvm> {
        if let Some(function) = self
            .module
            .get_function("__rt__existential_lookup_conformance")
        {
            return function;
        }
        let pointer = self.context.ptr_type(AddressSpace::default());
        self.module.add_function(
            "__rt__existential_lookup_conformance",
            pointer.fn_type(&[pointer.into(), pointer.into()], false),
            Some(Linkage::External),
        )
    }

    fn preserve_diagnostic_frame(&self, function: FunctionValue<'llvm>) {
        let inline_hint = Attribute::get_named_enum_kind_id("inlinehint");
        if inline_hint != 0 {
            function.remove_enum_attribute(AttributeLoc::Function, inline_hint);
        }
        add_llvm_enum_function_attribute(self.context, function, "noinline");
        // Caller maps may omit managed-call arguments because the callee's
        // entry map protects them. Tail-call elimination would erase that
        // physical callee frame just as surely as inlining does. This matters
        // even for a rootless poll: the managed caller may still depend on the
        // frame boundary to transfer root ownership.
        add_llvm_string_function_attribute(self.context, function, "disable-tail-calls", "true");
        // A stack-map intrinsic does not itself guarantee unwind metadata. The
        // runtime still has to walk through rootless collecting frames to
        // mapped callers, so request synchronous unwind tables for every
        // collecting frame. Value 1 is LLVM's UWTableKind::Sync.
        add_llvm_enum_function_attribute_with_value(self.context, function, "uwtable", 1);
    }

    fn lower_statement(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        stmt: &mir::Statement<'gcx>,
    ) -> CompileResult<()> {
        match &stmt.kind {
            mir::StatementKind::SourceScope(scope) => {
                self.current_source_scope = *scope;
            }
            mir::StatementKind::StorageLive(local) => {
                self.zero_gc_local(body, locals, *local);
            }
            mir::StatementKind::StorageDead(_) => {}
            mir::StatementKind::GcSafepoint(_) => self.emit_gc_poll(stmt.span),
            mir::StatementKind::SetInitialized(_) => {}
            mir::StatementKind::Assign(place, rvalue) => {
                if self.try_lower_large_place_move(body, locals, place, rvalue)? {
                    return Ok(());
                }
                if self.try_lower_repeat_memset(body, locals, place, rvalue)? {
                    return Ok(());
                }
                let dest_ty = self.place_ty(body, place);

                if let Some(value) = self.lower_rvalue(body, locals, dest_ty, rvalue)? {
                    self.store_place(place, body, locals, value)?;
                }
            }
            mir::StatementKind::KeepAlive(_) => {}
            mir::StatementKind::SetDiscriminant {
                place,
                variant_index,
            } => {
                let ptr = self.project_place(place, body, locals)?;
                let place_ty = self.place_ty(body, place);
                let (def, adt_args) = match place_ty.kind() {
                    TyKind::Adt(def, args) if def.kind == crate::sema::models::AdtKind::Enum => {
                        (def, args)
                    }
                    _ => panic!(
                        "set_discriminant on non-enum type {}",
                        place_ty.format(self.gcx)
                    ),
                };
                let layout = self.enum_layout_for(def.id, adt_args);
                if let Some(npo) = layout.npo {
                    // NPO: setting to the null/unit variant stores all-zero bits;
                    // setting to the payload variant is a no-op (the value itself
                    // serves as the discriminant).
                    if variant_index.index() == npo.null_variant {
                        let npo_ty = self.lower_ty(place_ty).expect("NPO enum type");
                        let _ = self.builder.build_store(ptr, npo_ty.const_zero()).unwrap();
                    }
                } else {
                    let enum_ty = self.lower_ty(place_ty).expect("enum");
                    let enum_struct = enum_ty.into_struct_type();
                    let discr_ptr = self
                        .builder
                        .build_struct_gep(enum_struct, ptr, 0, "enum_discr_ptr")
                        .unwrap();
                    let discr_val = layout
                        .discr_ty
                        .const_int(variant_index.index() as u64, false);
                    let _ = self.builder.build_store(discr_ptr, discr_val).unwrap();
                }
            }
            mir::StatementKind::Nop => {}
        }
        Ok(())
    }

    fn try_lower_large_place_move(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        destination: &Place<'gcx>,
        rvalue: &mir::Rvalue<'gcx>,
    ) -> CompileResult<bool> {
        let source = match rvalue {
            // A MIR move changes ownership bookkeeping, not the bytes needed
            // at the destination. Treat it like a copy here so large moved
            // arrays do not become giant first-class LLVM aggregate values.
            mir::Rvalue::Use(op) => match place_operand(op) {
                Some(source) => source,
                None => return Ok(false),
            },
            _ => return Ok(false),
        };

        let dest_ty = self.place_ty(body, destination);
        let src_ty = self.place_ty(body, source);
        let Some(dest_llvm_ty) = self.lower_ty(dest_ty) else {
            return Ok(false);
        };
        let Some(src_llvm_ty) = self.lower_ty(src_ty) else {
            return Ok(false);
        };

        let dest_size = self.target_data.get_store_size(&dest_llvm_ty);
        if dest_size == 0 || dest_size < LARGE_AGGREGATE_MOVE_MEMMOVE_THRESHOLD_BYTES {
            return Ok(false);
        }

        let src_size = self.target_data.get_store_size(&src_llvm_ty);
        if src_size != dest_size {
            return Ok(false);
        }

        let Some(dest_ptr) = self.place_address(body, locals, destination)? else {
            return Ok(false);
        };
        let Some(src_ptr) = self.place_address(body, locals, source)? else {
            return Ok(false);
        };

        let dest_align = self.target_data.get_abi_alignment(&dest_llvm_ty).max(1);
        let src_align = self.target_data.get_abi_alignment(&src_llvm_ty).max(1);
        let count = self.usize_ty.const_int(dest_size, false);

        // Use memmove for large aggregate assignments so we avoid materializing
        // giant by-value load/store chains in the backend. Values holding
        // pointers copy each word with one unordered atomic access instead:
        // libc memmove may move a pointer-aligned word in pieces.
        let word = self.target_data.get_pointer_byte_size(None);
        if (llvm_type_contains_pointer(dest_llvm_ty)
            || !self.gc_layout_nodes_for_ty(dest_ty).is_empty())
            && dest_size % u64::from(word) == 0
            && dest_align >= word
            && src_align >= word
        {
            self.build_element_atomic_memmove(dest_ptr, src_ptr, count, word);
        } else {
            let _ = self
                .builder
                .build_memmove(dest_ptr, dest_align, src_ptr, src_align, count)
                .unwrap();
        }

        Ok(true)
    }

    fn lower_rvalue(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        dest_ty: Ty<'gcx>,
        rvalue: &mir::Rvalue<'gcx>,
    ) -> CompileResult<Option<BasicValueEnum<'llvm>>> {
        let value = match rvalue {
            mir::Rvalue::Alloc { ty } => Some(self.lower_gc_alloc(*ty)?),
            mir::Rvalue::Use(op) => self.eval_operand(body, locals, op)?,
            mir::Rvalue::CopyValue { source } => {
                let value = self.load_place(body, locals, source);
                {
                    let ty = self.place_ty(body, source);
                    return Ok(value.map(|value| self.copy_gc_value(ty, value)));
                }
            }
            mir::Rvalue::UnaryOp { operand, op } => {
                let operand = match self.eval_operand(body, locals, operand)? {
                    Some(val) => val,
                    None => return Ok(None),
                };
                Some(self.lower_unary(dest_ty, *op, operand))
            }
            mir::Rvalue::BinaryOp { lhs, rhs, op } => {
                let lhs_ty = self.operand_ty(body, lhs);
                let lhs = match self.eval_operand(body, locals, lhs)? {
                    Some(val) => val,
                    None => return Ok(None),
                };
                let rhs = match self.eval_operand(body, locals, rhs)? {
                    Some(val) => val,
                    None => return Ok(None),
                };
                self.lower_binary(lhs_ty, *op, lhs, rhs)
            }
            mir::Rvalue::Cast { operand, ty, kind } => {
                let from_ty = self.operand_ty(body, operand);
                let val = match self.eval_operand(body, locals, operand)? {
                    Some(val) => val,
                    // `()` has no LLVM value, but its existential box still
                    // needs a payload and witness tables; boxing ignores the
                    // placeholder for a type without storage.
                    None if matches!(ty.kind(), TyKind::BoxedExistential { .. })
                        && self.mono_ty_if_resolved(from_ty) == self.gcx.types.void =>
                    {
                        self.context.const_struct(&[], false).into()
                    }
                    None => return Ok(None),
                };
                match kind {
                    mir::CastKind::Numeric => {
                        if matches!(ty.kind(), TyKind::BoxedExistential { .. }) {
                            let value = self.lower_boxed_existential(from_ty, *ty, val)?;
                            return Ok(Some(value));
                        }
                        let Some(value) = self.lower_cast(from_ty, *ty, val) else {
                            panic!(
                                "ICE: unhandled numeric cast from {} to {}",
                                from_ty.format(self.gcx),
                                ty.format(self.gcx)
                            );
                        };
                        return Ok(Some(value));
                    }
                    mir::CastKind::BoxExistential => {
                        let value = self.lower_boxed_existential(from_ty, *ty, val)?;
                        return Ok(Some(value));
                    }
                    mir::CastKind::ClassObjectOwner => {
                        let pointer = self.context.ptr_type(AddressSpace::default());
                        let first = self
                            .builder
                            .build_extract_value(val.into_struct_value(), 0, "class_object_source")
                            .unwrap()
                            .into_pointer_value();
                        let owner = if self
                            .gcx
                            .existential_requires_interface(from_ty, hir::StdItem::AnyObject)
                        {
                            self.builder
                                .build_load(pointer, first, "erased_class_object_owner")
                                .unwrap()
                        } else if self.gcx.uses_native_class_handle(from_ty) {
                            first.into()
                        } else {
                            self.gcx.dcx().emit_error(
                                "object ownership extraction requires a class-only value".into(),
                                self.current_span,
                            );
                            return Err(crate::error::ReportedError);
                        };
                        return Ok(Some(owner));
                    }
                    mir::CastKind::ClassSelfResult => {
                        let target = self.mono_ty(*ty);
                        if !self.gcx.is_class_subtype(target, from_ty) {
                            self.gcx.dcx().emit_error(
                                "invalid dynamic Self result adaptation".into(),
                                self.current_span,
                            );
                            return Err(crate::error::ReportedError);
                        }
                        return Ok(Some(val));
                    }
                    mir::CastKind::ClassUpcast => {
                        let target = self.mono_ty(*ty);
                        let valid = self.gcx.is_class_subtype(from_ty, target);
                        if !valid {
                            self.gcx
                                .dcx()
                                .emit_error("invalid class upcast".into(), self.current_span);
                            return Err(crate::error::ReportedError);
                        }
                        return Ok(Some(val));
                    }
                    mir::CastKind::ClassFromOwner => {
                        let header = self
                            .lower_ty(*ty)
                            .expect("class handle")
                            .into_struct_type()
                            .get_undef();
                        let value = self
                            .builder
                            .build_insert_value(
                                header,
                                val.into_pointer_value(),
                                0,
                                "class_from_owner",
                            )
                            .unwrap()
                            .into_struct_value();
                        return Ok(Some(value.into()));
                    }
                    mir::CastKind::NativeClassHandle => {
                        let concrete = self.mono_ty(*ty);
                        if !self.gcx.uses_native_class_handle(concrete) {
                            self.gcx.dcx().emit_error(format!("native class ownership conversion requires a concrete class handle, found {}", concrete.format(self.gcx)).into(), self.current_span);
                            return Err(crate::error::ReportedError);
                        }
                        let owner = if self.gcx.uses_native_class_handle(from_ty) {
                            self.builder
                                .build_extract_value(
                                    val.into_struct_value(),
                                    0,
                                    "transferred_class_owner",
                                )
                                .unwrap()
                                .into_pointer_value()
                        } else if matches!(from_ty.kind(), TyKind::Pointer(..)) {
                            val.into_pointer_value()
                        } else {
                            self.gcx.dcx().emit_error("class ownership transfer requires a strong handle or owned raw obligation".into(), self.current_span);
                            return Err(crate::error::ReportedError);
                        };
                        if self.gcx.is_class_type(concrete) {
                            let descriptor = self.class_descriptor(concrete)?;
                            let ptr = self.context.ptr_type(AddressSpace::default());
                            let set = self.get_or_add_external_function(
                                "__gc__class_initialize",
                                self.context
                                    .void_type()
                                    .fn_type(&[ptr.into(), ptr.into()], false),
                            );
                            self.builder
                                .build_call(set, &[owner.into(), descriptor.into()], "")
                                .unwrap();
                        }
                        let header = self
                            .lower_ty(*ty)
                            .expect("class handle")
                            .into_struct_type()
                            .get_undef();
                        let value = self
                            .builder
                            .build_insert_value(header, owner, 0, "owned_class_handle")
                            .unwrap()
                            .into_struct_value();
                        return Ok(Some(value.into()));
                    }
                    mir::CastKind::ExistentialUpcast => {
                        let value = self.lower_existential_upcast(from_ty, *ty, val)?;
                        return Ok(Some(value));
                    }
                    mir::CastKind::ExistentialTypeIs { target } => {
                        let value = self.lower_existential_type_is(from_ty, *target, val)?;
                        return Ok(Some(value));
                    }
                    mir::CastKind::ExistentialTryCast { target } => {
                        let value = self.lower_existential_try_cast(from_ty, *target, *ty, val)?;
                        return Ok(Some(value));
                    }
                    mir::CastKind::Pointer => {
                        let Some(value) = self.lower_cast(from_ty, *ty, val) else {
                            panic!(
                                "ICE: unhandled pointer cast from {} to {}",
                                from_ty.format(self.gcx),
                                ty.format(self.gcx)
                            );
                        };
                        return Ok(Some(value));
                    }
                    mir::CastKind::ClosureToFnPointer => {
                        let value = self.lower_closure_to_fn_pointer(from_ty, *ty)?;
                        return Ok(Some(value));
                    }
                }
            }
            mir::Rvalue::Ref { place, .. } | mir::Rvalue::CleanupAddress { place } => {
                // References to uninhabited / otherwise unrepresentable locals can
                // still appear in MIR around diverging async awaits (for example,
                // awaiting `Task[!]`). Those locals have no LLVM storage layout, so
                // project_place cannot materialize a real address. Provide a dummy
                // stack slot instead; code that would meaningfully read/write the
                // pointee is unreachable because the value never exists.
                let place_ty = self.place_ty(body, place);
                let place_llvm_ty = self.lower_ty(place_ty);
                let place_has_no_storage = match place_llvm_ty {
                    None => true,
                    Some(llvm_ty) => self.target_data.get_store_size(&llvm_ty) == 0,
                };
                // A managed zero-sized referent may already have stable
                // promoted storage. Preserve that selected address.
                let ptr = if matches!(locals[place.local.index()], LocalStorage::Value(None))
                    || (!true && place_has_no_storage)
                {
                    // Keep references non-null even for zero-sized pointees.
                    self.build_entry_alloca(self.context.i8_type(), "ref_dummy")
                } else {
                    self.project_place(place, body, locals)?
                };
                if matches!(rvalue, mir::Rvalue::CleanupAddress { .. }) {
                    Some(ptr.into())
                } else {
                    Some(self.lexical_reference(ptr))
                }
            }
            mir::Rvalue::Discriminant { place } => {
                let ptr = self.project_place(place, body, locals)?;
                let place_ty = self.place_ty(body, place);
                let (def, adt_args) = match place_ty.kind() {
                    TyKind::Adt(def, args) if def.kind == crate::sema::models::AdtKind::Enum => {
                        (def, args)
                    }
                    _ => panic!(
                        "ICE: discriminant on non-enum type {} while lowering {}",
                        place_ty.format(self.gcx),
                        self.gcx
                            .symbol_text(self.gcx.definition_ident(body.owner).symbol),
                    ),
                };
                let layout = self.enum_layout_for(def.id, adt_args);
                if let Some(npo) = layout.npo {
                    // NPO: discriminant is derived from a null check on the niche pointer.
                    let npo_ty = self.lower_ty(place_ty).expect("npo enum type");
                    let loaded = self.builder.build_load(npo_ty, ptr, "npo_val").unwrap();
                    let niche_ptr = match loaded {
                        BasicValueEnum::PointerValue(ptr) => ptr,
                        BasicValueEnum::StructValue(struct_val) => self
                            .builder
                            .build_extract_value(struct_val, 0, "npo_data_ptr")
                            .unwrap()
                            .into_pointer_value(),
                        _ => panic!(
                            "ICE: NPO enum lowered to unsupported LLVM type for {}",
                            place_ty.format(self.gcx)
                        ),
                    };
                    let is_null = self
                        .builder
                        .build_is_null(niche_ptr, "npo_is_null")
                        .unwrap();
                    let discr = self
                        .builder
                        .build_select(
                            is_null,
                            self.usize_ty.const_int(npo.null_variant as u64, false),
                            self.usize_ty.const_int(npo.payload_variant as u64, false),
                            "npo_discr",
                        )
                        .unwrap();
                    Some(discr.as_basic_value_enum())
                } else {
                    let enum_ty = self.lower_ty(place_ty).expect("enum");
                    let enum_struct = enum_ty.into_struct_type();
                    let discr_ptr = self
                        .builder
                        .build_struct_gep(enum_struct, ptr, 0, "enum_discr_ptr")
                        .unwrap();
                    // The tag is stored at its own narrow width; MIR compares
                    // discriminants as `usize`, so widen on the way out.
                    let raw = self
                        .builder
                        .build_load(layout.discr_ty, discr_ptr, "enum_discr")
                        .unwrap()
                        .into_int_value();
                    let discr_val = self
                        .builder
                        .build_int_z_extend_or_bit_cast(raw, self.usize_ty, "enum_discr_usize")
                        .unwrap();
                    Some(discr_val.as_basic_value_enum())
                }
            }
            mir::Rvalue::Aggregate { kind, fields } => match kind {
                mir::AggregateKind::Array { .. } => {
                    // Arrays of unit/unrepresented elements have no bytes.
                    // Element expressions have already been evaluated into
                    // operands by MIR; there is no aggregate value to build.
                    let Some(llvm_ty) = self.lower_ty(dest_ty) else {
                        return Ok(None);
                    };
                    let arr_ty = llvm_ty.into_array_type();
                    let mut agg = arr_ty.get_undef();
                    for (idx, field) in fields.iter_enumerated() {
                        let Some(val) = self.eval_operand(body, locals, field)? else {
                            return Ok(None);
                        };
                        let insert_idx =
                            u32::try_from(idx.index()).expect("array element index fits in u32");
                        let insert = self
                            .builder
                            .build_insert_value(agg, val, insert_idx, "array_ins")
                            .unwrap();
                        agg = insert.into_array_value();
                    }
                    Some(agg.as_basic_value_enum())
                }
                _ if kind.noncollecting_enum_ctor(self.gcx).is_some() => {
                    self.lower_noncollecting_enum(body, locals, dest_ty, kind, fields)?
                }
                _ => unreachable!("payload aggregates should be lowered in MIR"),
            },
            mir::Rvalue::Repeat { operand, count, .. } => {
                let arr_ty = match self.lower_ty(dest_ty) {
                    Some(ty) => ty.into_array_type(),
                    None => return Ok(None),
                };
                if self.repeat_operand_is_zero(operand) {
                    return Ok(Some(arr_ty.const_zero().as_basic_value_enum()));
                }
                let Some(val) = self.eval_operand(body, locals, operand)? else {
                    return Ok(None);
                };
                // Construct scalar constants once instead of interning N
                // intermediate N-element constants (quadratic compiler memory).
                let constant = match val {
                    BasicValueEnum::IntValue(v) if v.is_const() => {
                        Some(v.get_type().const_array(&vec![v; *count]))
                    }
                    BasicValueEnum::FloatValue(v) if v.is_const() => {
                        Some(v.get_type().const_array(&vec![v; *count]))
                    }
                    BasicValueEnum::PointerValue(v) if v.is_const() => {
                        Some(v.get_type().const_array(&vec![v; *count]))
                    }
                    _ => None,
                };
                if let Some(array) = constant {
                    return Ok(Some(array.into()));
                }
                let mut agg = arr_ty.get_undef();
                for i in 0..*count {
                    let element = val;
                    let insert_idx =
                        u32::try_from(i).expect("repeat count should fit in u32 for LLVM array");
                    let insert = self
                        .builder
                        .build_insert_value(agg, element, insert_idx, "repeat_ins")
                        .unwrap();
                    agg = insert.into_array_value();
                }
                Some(agg.as_basic_value_enum())
            }
            mir::Rvalue::Zeroed { ty } => self
                .lower_ty(*ty)
                .map(|llvm_ty| llvm_ty.const_zero().as_basic_value_enum()),
        };
        Ok(value)
    }

    /// Snapshot every field before touching destination storage. The MIR
    /// allowlist excludes erased/aggregate copies, so none of these operations
    /// can collect. The private scratch defines the tag and every payload word;
    /// LLVM can promote it instead of carrying inactive bytes across a poll.
    fn lower_noncollecting_enum(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        ty: Ty<'gcx>,
        kind: &mir::AggregateKind<'gcx>,
        fields: &index_vec::IndexVec<crate::thir::FieldIndex, Operand<'gcx>>,
    ) -> CompileResult<Option<BasicValueEnum<'llvm>>> {
        let ctor = kind
            .noncollecting_enum_ctor(self.gcx)
            .expect("noncollecting enum");
        if let Some(value) = self.lower_enum_unit_variant_const(ty, ctor) {
            return Ok(Some(value));
        }
        let TyKind::Adt(def, args) = ty.kind() else {
            unreachable!()
        };
        let mir::AggregateKind::Adt {
            variant_index: Some(index),
            ..
        } = kind
        else {
            unreachable!()
        };
        let layout = self.enum_layout_for(def.id, args);
        let values = fields
            .iter()
            .map(|field| {
                self.eval_operand(body, locals, field)
                    .map(|value| value.expect("scalar enum field"))
            })
            .collect::<CompileResult<Vec<_>>>()?;
        if let Some(npo) = layout.npo {
            if index.index() == npo.null_variant {
                assert!(values.is_empty());
                return Ok(Some(self.lower_ty(ty).expect("niche enum").const_zero()));
            }
            assert_eq!(index.index(), npo.payload_variant);
            assert_eq!(values.len(), 1);
            return Ok(Some(values[0]));
        }
        let enum_ty = self.lower_ty(ty).expect("enum layout");
        let scratch = self.build_entry_alloca(enum_ty, "enum_construct");
        self.builder
            .build_store(scratch, enum_ty.const_zero())
            .unwrap();
        if !values.is_empty() {
            let payload = self
                .builder
                .build_struct_gep(
                    enum_ty.into_struct_type(),
                    scratch,
                    layout.payload_field_index.expect("nonempty scalar payload"),
                    "enum_construct_payload",
                )
                .unwrap();
            let variant_ty = mir::enum_variant_tuple_ty(self.gcx, def.id, *index, args);
            let variant_ty = self
                .lower_ty(variant_ty)
                .expect("variant tuple")
                .into_struct_type();
            assert_eq!(values.len(), variant_ty.count_fields() as usize);
            for (field, value) in values.into_iter().enumerate() {
                let pointer = self
                    .builder
                    .build_struct_gep(variant_ty, payload, field as u32, "enum_construct_field")
                    .unwrap();
                self.builder.build_store(pointer, value).unwrap();
            }
        }
        let tag = self
            .builder
            .build_struct_gep(enum_ty.into_struct_type(), scratch, 0, "enum_construct_tag")
            .unwrap();
        self.builder
            .build_store(tag, layout.discr_ty.const_int(index.index() as u64, false))
            .unwrap();
        Ok(Some(
            self.builder
                .build_load(enum_ty, scratch, "enum_construct_value")
                .unwrap(),
        ))
    }

    fn repeat_operand_is_zero(&self, operand: &Operand<'gcx>) -> bool {
        let Operand::Constant(c) = operand else {
            return false;
        };
        matches!(
            c.value,
            mir::ConstantKind::Integer(0)
                | mir::ConstantKind::Bool(false)
                | mir::ConstantKind::Unit
        )
    }

    fn repeat_memset_byte_value(&self, operand: &Operand<'gcx>, elem_size: u64) -> Option<u8> {
        let Operand::Constant(c) = operand else {
            return None;
        };
        match c.value {
            mir::ConstantKind::Integer(i) => {
                if elem_size == 0 || elem_size > 8 {
                    return None;
                }
                let bytes = i.to_le_bytes();
                let fill = bytes[0];
                if bytes[..elem_size as usize].iter().all(|b| *b == fill) {
                    Some(fill)
                } else {
                    None
                }
            }
            mir::ConstantKind::Bool(b) => {
                if elem_size == 1 || !b {
                    Some(if b { 1 } else { 0 })
                } else {
                    None
                }
            }
            mir::ConstantKind::Unit => Some(0),
            _ => None,
        }
    }

    fn try_lower_repeat_memset(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        place: &Place<'gcx>,
        rvalue: &mir::Rvalue<'gcx>,
    ) -> CompileResult<bool> {
        if !self.repeat_memset_enabled {
            return Ok(false);
        }
        let mir::Rvalue::Repeat {
            operand,
            count,
            element,
        } = rvalue
        else {
            return Ok(false);
        };
        if *count == 0 {
            return Ok(false);
        }
        let Some(dest_ptr) = self.place_address(body, locals, place)? else {
            return Ok(false);
        };
        let Some(llvm_elem_ty) = self.lower_ty(*element) else {
            return Ok(false);
        };
        let elem_size = self.target_data.get_store_size(&llvm_elem_ty);
        if elem_size == 0 {
            return Ok(false);
        }
        let byte_count = (*count as u64)
            .checked_mul(elem_size)
            .expect("repeat byte count should fit in u64");
        if byte_count < self.repeat_memset_min_bytes {
            return Ok(false);
        }

        let Some(fill_byte) = self.repeat_memset_byte_value(operand, elem_size) else {
            return Ok(false);
        };

        let fill_val = self.context.i8_type().const_int(fill_byte as u64, false);
        let count_val = self.usize_ty.const_int(byte_count, false);
        // Keep alignment conservative for projected destinations.
        let _ = self
            .builder
            .build_memset(dest_ptr, 1, fill_val, count_val)
            .unwrap();

        Ok(true)
    }

    fn lower_unary(
        &mut self,
        dest_ty: Ty<'gcx>,
        op: mir::UnaryOperator,
        operand: BasicValueEnum<'llvm>,
    ) -> BasicValueEnum<'llvm> {
        let dest_ty = self.mono_ty(dest_ty);
        match op {
            mir::UnaryOperator::LogicalNot => {
                let val = operand.into_int_value();
                self.builder
                    .build_not(val, "bool_not")
                    .unwrap()
                    .as_basic_value_enum()
            }
            mir::UnaryOperator::Negate => match dest_ty.kind() {
                TyKind::Float(_) => {
                    let val = operand.into_float_value();
                    self.builder
                        .build_float_neg(val, "neg")
                        .unwrap()
                        .as_basic_value_enum()
                }
                _ => {
                    let val = operand.into_int_value();
                    self.builder
                        .build_int_neg(val, "neg")
                        .unwrap()
                        .as_basic_value_enum()
                }
            },
            mir::UnaryOperator::BitwiseNot => {
                let val = operand.into_int_value();
                self.builder
                    .build_not(val, "not")
                    .unwrap()
                    .as_basic_value_enum()
            }
        }
    }

    fn lower_binary(
        &mut self,
        operand_ty: Ty<'gcx>,
        op: mir::BinaryOperator,
        lhs: BasicValueEnum<'llvm>,
        rhs: BasicValueEnum<'llvm>,
    ) -> Option<BasicValueEnum<'llvm>> {
        let operand_ty = self.mono_ty(operand_ty);
        let result = match operand_ty.kind() {
            TyKind::Float(_) => {
                let lhs = lhs.into_float_value();
                let rhs = rhs.into_float_value();
                match op {
                    mir::BinaryOperator::Add => self
                        .builder
                        .build_float_add(lhs, rhs, "add")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::Sub => self
                        .builder
                        .build_float_sub(lhs, rhs, "sub")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::Mul => self
                        .builder
                        .build_float_mul(lhs, rhs, "mul")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::Div => self
                        .builder
                        .build_float_div(lhs, rhs, "div")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::Rem => self
                        .builder
                        .build_float_rem(lhs, rhs, "rem")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::Eql => self
                        .builder
                        .build_float_compare(FloatPredicate::OEQ, lhs, rhs, "eq")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::Neq => self
                        .builder
                        .build_float_compare(FloatPredicate::UNE, lhs, rhs, "neq")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::Gt => self
                        .builder
                        .build_float_compare(FloatPredicate::OGT, lhs, rhs, "gt")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::Lt => self
                        .builder
                        .build_float_compare(FloatPredicate::OLT, lhs, rhs, "lt")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::Geq => self
                        .builder
                        .build_float_compare(FloatPredicate::OGE, lhs, rhs, "ge")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::Leq => self
                        .builder
                        .build_float_compare(FloatPredicate::OLE, lhs, rhs, "le")
                        .unwrap()
                        .as_basic_value_enum(),
                    _ => return None,
                }
            }
            TyKind::Bool => {
                let lhs = lhs.into_int_value();
                let rhs = rhs.into_int_value();
                match op {
                    mir::BinaryOperator::BitAnd => self
                        .builder
                        .build_and(lhs, rhs, "and")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::BitOr => self
                        .builder
                        .build_or(lhs, rhs, "or")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::BitXor => self
                        .builder
                        .build_xor(lhs, rhs, "xor")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::Eql => self
                        .builder
                        .build_int_compare(IntPredicate::EQ, lhs, rhs, "eq")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::Neq => self
                        .builder
                        .build_int_compare(IntPredicate::NE, lhs, rhs, "neq")
                        .unwrap()
                        .as_basic_value_enum(),
                    _ => return None,
                }
            }
            TyKind::Pointer(..) | TyKind::Reference(..) => {
                let ptr_int_ty = self.context.ptr_sized_int_type(&self.target_data, None);
                let pointer_int = |value, name| {
                    let pointer = self.reference_data(value);
                    self.builder
                        .build_ptr_to_int(pointer, ptr_int_ty, name)
                        .unwrap()
                };
                let lhs = pointer_int(lhs, "ptr_l");
                let rhs = pointer_int(rhs, "ptr_r");
                match op {
                    mir::BinaryOperator::Eql => self
                        .builder
                        .build_int_compare(IntPredicate::EQ, lhs, rhs, "ptr_eq")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::Neq => self
                        .builder
                        .build_int_compare(IntPredicate::NE, lhs, rhs, "ptr_neq")
                        .unwrap()
                        .as_basic_value_enum(),
                    _ => return None,
                }
            }
            TyKind::Int(_) | TyKind::UInt(_) | TyKind::Rune => {
                let lhs = lhs.into_int_value();
                let rhs = rhs.into_int_value();
                let signed = is_signed(operand_ty);
                match op {
                    mir::BinaryOperator::Add => self
                        .builder
                        .build_int_add(lhs, rhs, "add")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::Sub => self
                        .builder
                        .build_int_sub(lhs, rhs, "sub")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::Mul => self
                        .builder
                        .build_int_mul(lhs, rhs, "mul")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::Div => {
                        if signed {
                            self.builder
                                .build_int_signed_div(lhs, rhs, "div")
                                .unwrap()
                                .as_basic_value_enum()
                        } else {
                            self.builder
                                .build_int_unsigned_div(lhs, rhs, "div")
                                .unwrap()
                                .as_basic_value_enum()
                        }
                    }
                    mir::BinaryOperator::Rem => {
                        if signed {
                            self.builder
                                .build_int_signed_rem(lhs, rhs, "rem")
                                .unwrap()
                                .as_basic_value_enum()
                        } else {
                            self.builder
                                .build_int_unsigned_rem(lhs, rhs, "rem")
                                .unwrap()
                                .as_basic_value_enum()
                        }
                    }
                    mir::BinaryOperator::BitAnd => self
                        .builder
                        .build_and(lhs, rhs, "and")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::BitOr => self
                        .builder
                        .build_or(lhs, rhs, "or")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::BitXor => self
                        .builder
                        .build_xor(lhs, rhs, "xor")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::BitShl => {
                        let amount = self.mask_shift_amount(lhs, rhs);
                        self.builder
                            .build_left_shift(lhs, amount, "shl")
                            .unwrap()
                            .as_basic_value_enum()
                    }
                    mir::BinaryOperator::BitShr => {
                        let amount = self.mask_shift_amount(lhs, rhs);
                        self.builder
                            .build_right_shift(lhs, amount, signed, "shr")
                            .unwrap()
                            .as_basic_value_enum()
                    }
                    mir::BinaryOperator::Eql => self
                        .builder
                        .build_int_compare(IntPredicate::EQ, lhs, rhs, "eq")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::Neq => self
                        .builder
                        .build_int_compare(IntPredicate::NE, lhs, rhs, "neq")
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::Gt => self
                        .builder
                        .build_int_compare(
                            if signed {
                                IntPredicate::SGT
                            } else {
                                IntPredicate::UGT
                            },
                            lhs,
                            rhs,
                            "gt",
                        )
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::Lt => self
                        .builder
                        .build_int_compare(
                            if signed {
                                IntPredicate::SLT
                            } else {
                                IntPredicate::ULT
                            },
                            lhs,
                            rhs,
                            "lt",
                        )
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::Geq => self
                        .builder
                        .build_int_compare(
                            if signed {
                                IntPredicate::SGE
                            } else {
                                IntPredicate::UGE
                            },
                            lhs,
                            rhs,
                            "ge",
                        )
                        .unwrap()
                        .as_basic_value_enum(),
                    mir::BinaryOperator::Leq => self
                        .builder
                        .build_int_compare(
                            if signed {
                                IntPredicate::SLE
                            } else {
                                IntPredicate::ULE
                            },
                            lhs,
                            rhs,
                            "le",
                        )
                        .unwrap()
                        .as_basic_value_enum(),
                }
            }
            _ => return None,
        };
        Some(result)
    }

    /// Mask a shift amount to the operand bit width so unchecked shifts wrap
    /// (shift modulo width) instead of producing LLVM poison. Checked shifts
    /// are lowered through `__intrinsic_checked_shl`/`shr` and panic before
    /// an out-of-range amount reaches the shift instruction.
    fn mask_shift_amount(&mut self, lhs: IntValue<'llvm>, rhs: IntValue<'llvm>) -> IntValue<'llvm> {
        let bits = lhs.get_type().get_bit_width() as u64;
        let mask = rhs.get_type().const_int(bits - 1, false);
        self.builder.build_and(rhs, mask, "shift_mask").unwrap()
    }

    /// Lower `__intrinsic_wrapping_{add,sub,mul}` to plain two's-complement
    /// LLVM arithmetic and `__intrinsic_overflows_{add,sub,mul}` to the flag of
    /// the matching `llvm.*.with.overflow` intrinsic. Neither traps, and the
    /// lowering ignores the overflow policy: std bodies that use them keep
    /// their meaning when inlined or specialized into a checked package.
    fn lower_intrinsic_integer_arith(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
        name: &str,
    ) -> CompileResult<bool> {
        let (overflow_flag, op) = match name {
            "__intrinsic_wrapping_add" => (false, "add"),
            "__intrinsic_wrapping_sub" => (false, "sub"),
            "__intrinsic_wrapping_mul" => (false, "mul"),
            "__intrinsic_overflows_add" => (true, "add"),
            "__intrinsic_overflows_sub" => (true, "sub"),
            "__intrinsic_overflows_mul" => (true, "mul"),
            _ => return Ok(false),
        };
        let operand_ty = args.first().map(|arg| self.operand_ty(body, arg));
        let Some(operand_ty) = operand_ty
            .filter(|ty| args.len() == 2 && matches!(ty.kind(), TyKind::Int(_) | TyKind::UInt(_)))
        else {
            self.gcx.dcx().emit_error(
                format!("{name} requires two operands of one integer type"),
                None,
            );
            return Err(crate::error::ReportedError);
        };
        let lhs = self
            .eval_operand(body, locals, &args[0])?
            .expect("integer arithmetic operand must have a value")
            .into_int_value();
        let rhs = self
            .eval_operand(body, locals, &args[1])?
            .expect("integer arithmetic operand must have a value")
            .into_int_value();
        let result = if overflow_flag {
            let signed = is_signed(operand_ty);
            let intrinsic_name =
                format!("llvm.{}{op}.with.overflow", if signed { "s" } else { "u" });
            let intrinsic = Intrinsic::find(&intrinsic_name)
                .unwrap_or_else(|| panic!("ICE: missing LLVM intrinsic {intrinsic_name}"));
            let decl = intrinsic
                .get_declaration(&self.module, &[lhs.get_type().as_basic_type_enum()])
                .unwrap_or_else(|| panic!("ICE: cannot declare LLVM intrinsic {intrinsic_name}"));
            let call = self
                .builder
                .build_call(decl, &[lhs.into(), rhs.into()], op)
                .unwrap();
            let pair = call
                .try_as_basic_value()
                .basic()
                .expect("overflow intrinsic returns {value, flag}")
                .into_struct_value();
            self.builder
                .build_extract_value(pair, 1, "arith_ovf")
                .unwrap()
        } else {
            match op {
                "add" => self.builder.build_int_add(lhs, rhs, "wrapping_add"),
                "sub" => self.builder.build_int_sub(lhs, rhs, "wrapping_sub"),
                _ => self.builder.build_int_mul(lhs, rhs, "wrapping_mul"),
            }
            .unwrap()
            .as_basic_value_enum()
        };
        self.store_place(destination, body, locals, result)?;
        Ok(true)
    }

    /// Lower `__intrinsic_{ctpop,ctlz,cttz,bswap,bitreverse,fshl,fshr}` to
    /// their LLVM scalar intrinsics. `ctlz` and `cttz` always pass
    /// `is_zero_poison = false`, `bswap` on `i8` lowers to identity (LLVM
    /// rejects `llvm.bswap.i8`), and `fshl`/`fshr` narrow or zero-extend the
    /// `uint32` shift count to the operand bit width so LLVM applies modulo
    /// bit-width rotation safely for every shift count.
    fn lower_intrinsic_integer_bit(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
        name: &str,
    ) -> CompileResult<bool> {
        let is_bit_intrinsic = matches!(
            name,
            "__intrinsic_ctpop"
                | "__intrinsic_ctlz"
                | "__intrinsic_cttz"
                | "__intrinsic_bswap"
                | "__intrinsic_bitreverse"
                | "__intrinsic_fshl"
                | "__intrinsic_fshr"
        );
        if !is_bit_intrinsic {
            return Ok(false);
        }

        let result = match name {
            "__intrinsic_ctpop" | "__intrinsic_ctlz" | "__intrinsic_cttz" => {
                let operand_ty = args.first().map(|arg| self.operand_ty(body, arg));
                if args.len() != 1
                    || !operand_ty
                        .is_some_and(|ty| matches!(ty.kind(), TyKind::Int(_) | TyKind::UInt(_)))
                {
                    self.gcx.dcx().emit_error(
                        format!("{name} requires one integer operand"),
                        None,
                    );
                    return Err(crate::error::ReportedError);
                }
                let val = self
                    .eval_operand(body, locals, &args[0])?
                    .expect("integer bit operand must have a value")
                    .into_int_value();
                let int_ty = val.get_type();
                let llvm_name = match name {
                    "__intrinsic_ctpop" => "llvm.ctpop",
                    "__intrinsic_ctlz" => "llvm.ctlz",
                    _ => "llvm.cttz",
                };
                let intrinsic = Intrinsic::find(llvm_name)
                    .unwrap_or_else(|| panic!("ICE: missing LLVM intrinsic {llvm_name}"));
                let decl = intrinsic
                    .get_declaration(&self.module, &[int_ty.as_basic_type_enum()])
                    .unwrap_or_else(|| panic!("ICE: cannot declare LLVM intrinsic {llvm_name}"));
                let call = if name == "__intrinsic_ctpop" {
                    self.builder
                        .build_call(decl, &[val.into()], "ctpop")
                        .unwrap()
                } else {
                    let zero_is_poison = self.context.bool_type().const_int(0, false);
                    self.builder
                        .build_call(decl, &[val.into(), zero_is_poison.into()], "ctz")
                        .unwrap()
                };
                let raw = call
                    .try_as_basic_value()
                    .basic()
                    .expect("bit-count intrinsic returns integer")
                    .into_int_value();
                let u32_ty = self.context.i32_type();
                let bits = int_ty.get_bit_width();
                let u32_val = if bits < 32 {
                    self.builder
                        .build_int_z_extend(raw, u32_ty, "bitcount_zext")
                        .unwrap()
                } else if bits > 32 {
                    self.builder
                        .build_int_truncate(raw, u32_ty, "bitcount_trunc")
                        .unwrap()
                } else {
                    raw
                };
                u32_val.as_basic_value_enum()
            }
            "__intrinsic_bswap" | "__intrinsic_bitreverse" => {
                let operand_ty = args.first().map(|arg| self.operand_ty(body, arg));
                if args.len() != 1
                    || !operand_ty
                        .is_some_and(|ty| matches!(ty.kind(), TyKind::Int(_) | TyKind::UInt(_)))
                {
                    self.gcx.dcx().emit_error(
                        format!("{name} requires one integer operand"),
                        None,
                    );
                    return Err(crate::error::ReportedError);
                }
                let val = self
                    .eval_operand(body, locals, &args[0])?
                    .expect("integer bit operand must have a value")
                    .into_int_value();
                let int_ty = val.get_type();
                if name == "__intrinsic_bswap" && int_ty.get_bit_width() <= 8 {
                    val.as_basic_value_enum()
                } else {
                    let llvm_name = if name == "__intrinsic_bswap" {
                        "llvm.bswap"
                    } else {
                        "llvm.bitreverse"
                    };
                    let intrinsic = Intrinsic::find(llvm_name)
                        .unwrap_or_else(|| panic!("ICE: missing LLVM intrinsic {llvm_name}"));
                    let decl = intrinsic
                        .get_declaration(&self.module, &[int_ty.as_basic_type_enum()])
                        .unwrap_or_else(|| {
                            panic!("ICE: cannot declare LLVM intrinsic {llvm_name}")
                        });
                    self.builder
                        .build_call(decl, &[val.into()], "bitop")
                        .unwrap()
                        .try_as_basic_value()
                        .basic()
                        .expect("bit intrinsic returns integer")
                }
            }
            "__intrinsic_fshl" | "__intrinsic_fshr" => {
                let valid = args.len() == 3
                    && matches!(
                        self.operand_ty(body, &args[0]).kind(),
                        TyKind::Int(_) | TyKind::UInt(_)
                    )
                    && matches!(
                        self.operand_ty(body, &args[1]).kind(),
                        TyKind::Int(_) | TyKind::UInt(_)
                    )
                    && matches!(
                        self.operand_ty(body, &args[2]).kind(),
                        TyKind::Int(_) | TyKind::UInt(_)
                    );
                if !valid {
                    self.gcx.dcx().emit_error(
                        format!("{name} requires two integer operands and an integer shift count"),
                        None,
                    );
                    return Err(crate::error::ReportedError);
                }
                let hi = self
                    .eval_operand(body, locals, &args[0])?
                    .expect("funnel-shift hi operand must have a value")
                    .into_int_value();
                let lo = self
                    .eval_operand(body, locals, &args[1])?
                    .expect("funnel-shift lo operand must have a value")
                    .into_int_value();
                let shift = self
                    .eval_operand(body, locals, &args[2])?
                    .expect("funnel-shift shift operand must have a value")
                    .into_int_value();
                let int_ty = hi.get_type();
                let target_bits = int_ty.get_bit_width();
                let shift_bits = shift.get_type().get_bit_width();
                let shift_cast = if shift_bits < target_bits {
                    self.builder
                        .build_int_z_extend(shift, int_ty, "fsh_shift_zext")
                        .unwrap()
                } else if shift_bits > target_bits {
                    self.builder
                        .build_int_truncate(shift, int_ty, "fsh_shift_trunc")
                        .unwrap()
                } else {
                    shift
                };
                let llvm_name = if name == "__intrinsic_fshl" {
                    "llvm.fshl"
                } else {
                    "llvm.fshr"
                };
                let intrinsic = Intrinsic::find(llvm_name)
                    .unwrap_or_else(|| panic!("ICE: missing LLVM intrinsic {llvm_name}"));
                let decl = intrinsic
                    .get_declaration(&self.module, &[int_ty.as_basic_type_enum()])
                    .unwrap_or_else(|| panic!("ICE: cannot declare LLVM intrinsic {llvm_name}"));
                self.builder
                    .build_call(decl, &[hi.into(), lo.into(), shift_cast.into()], "fsh")
                    .unwrap()
                    .try_as_basic_value()
                    .basic()
                    .expect("funnel-shift intrinsic returns integer")
            }
            _ => unreachable!(),
        };

        self.store_place(destination, body, locals, result)?;
        Ok(true)
    }

    /// Lower `__intrinsic_checked_{add,sub,mul,div,rem,shl,shr,neg}` calls
    /// emitted by the MIR builder when overflow checks are enabled. The
    /// panic branches go through the call's unwind edge, so defers and the
    /// logical stack unwind like any other panic.
    fn try_lower_checked_arith_call(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        span: crate::span::Span,
        func: &Operand<'gcx>,
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
        normal_bb: BasicBlock<'llvm>,
        unwind_bb: Option<BasicBlock<'llvm>>,
    ) -> CompileResult<bool> {
        let Operand::Constant(c) = func else {
            return Ok(false);
        };
        let mir::ConstantKind::Function(def_id, _, _) = c.value else {
            return Ok(false);
        };
        let Some(hir::Abi::Intrinsic) = self.gcx.get_signature(def_id).abi else {
            return Ok(false);
        };
        let ident = self.gcx.definition_ident(def_id);
        let name = self.gcx.symbol_text(ident.symbol);
        let op = match name.as_str() {
            "__intrinsic_checked_add" => "add",
            "__intrinsic_checked_sub" => "sub",
            "__intrinsic_checked_mul" => "mul",
            "__intrinsic_checked_div" => "div",
            "__intrinsic_checked_rem" => "rem",
            "__intrinsic_checked_shl" => "shl",
            "__intrinsic_checked_shr" => "shr",
            "__intrinsic_checked_neg" => "neg",
            _ => return Ok(false),
        };

        let operand_ty = self.operand_ty(body, &args[0]);
        let signed = is_signed(operand_ty);
        let lhs = self
            .eval_operand(body, locals, &args[0])?
            .expect("checked arithmetic operand must have a value")
            .into_int_value();
        let int_ty = lhs.get_type();
        let bits = int_ty.get_bit_width() as u64;

        let cont_bb = self.append_block_to_current_fn("checked_cont");

        let result = match op {
            "add" | "sub" | "mul" => {
                let rhs = self
                    .eval_operand(body, locals, &args[1])?
                    .expect("checked arithmetic operand must have a value")
                    .into_int_value();
                let intrinsic_name =
                    format!("llvm.{}{op}.with.overflow", if signed { "s" } else { "u" });
                let intrinsic = Intrinsic::find(&intrinsic_name)
                    .unwrap_or_else(|| panic!("ICE: missing LLVM intrinsic {intrinsic_name}"));
                let decl = intrinsic
                    .get_declaration(&self.module, &[int_ty.as_basic_type_enum()])
                    .unwrap_or_else(|| {
                        panic!("ICE: cannot declare LLVM intrinsic {intrinsic_name}")
                    });
                let call = self
                    .builder
                    .build_call(decl, &[lhs.into(), rhs.into()], op)
                    .unwrap();
                let pair = call
                    .try_as_basic_value()
                    .basic()
                    .expect("overflow intrinsic returns {value, flag}")
                    .into_struct_value();
                let result = self
                    .builder
                    .build_extract_value(pair, 0, "arith_val")
                    .unwrap();
                let overflowed = self
                    .builder
                    .build_extract_value(pair, 1, "arith_ovf")
                    .unwrap()
                    .into_int_value();
                let panic_bb = self.append_block_to_current_fn("arith_ovf_panic");
                let _ = self
                    .builder
                    .build_conditional_branch(overflowed, panic_bb, cont_bb)
                    .unwrap();
                let verb = match op {
                    "add" => "add",
                    "sub" => "subtract",
                    _ => "multiply",
                };
                self.builder.position_at_end(panic_bb);
                self.emit_arith_panic(
                    &format!("attempt to {verb} with overflow"),
                    span,
                    unwind_bb,
                )?;
                result
            }
            "div" | "rem" => {
                let rhs = self
                    .eval_operand(body, locals, &args[1])?
                    .expect("checked arithmetic operand must have a value")
                    .into_int_value();
                let (zero_msg, ovf_msg) = if op == "div" {
                    (
                        "attempt to divide by zero",
                        "attempt to divide with overflow",
                    )
                } else {
                    (
                        "attempt to calculate the remainder with a divisor of zero",
                        "attempt to calculate the remainder with overflow",
                    )
                };
                let zero_panic_bb = self.append_block_to_current_fn("div_zero_panic");
                let is_zero = self
                    .builder
                    .build_int_compare(IntPredicate::EQ, rhs, int_ty.const_zero(), "div_zero")
                    .unwrap();
                if signed {
                    // Signed division also overflows for MIN / -1.
                    let ovf_check_bb = self.append_block_to_current_fn("div_ovf_check");
                    let _ = self
                        .builder
                        .build_conditional_branch(is_zero, zero_panic_bb, ovf_check_bb)
                        .unwrap();
                    self.builder.position_at_end(ovf_check_bb);
                    let min = int_ty.const_int(1u64 << (bits - 1), false);
                    let is_min = self
                        .builder
                        .build_int_compare(IntPredicate::EQ, lhs, min, "div_lhs_min")
                        .unwrap();
                    let is_neg_one = self
                        .builder
                        .build_int_compare(
                            IntPredicate::EQ,
                            rhs,
                            int_ty.const_all_ones(),
                            "div_rhs_m1",
                        )
                        .unwrap();
                    let overflows = self
                        .builder
                        .build_and(is_min, is_neg_one, "div_ovf")
                        .unwrap();
                    let ovf_panic_bb = self.append_block_to_current_fn("div_ovf_panic");
                    let _ = self
                        .builder
                        .build_conditional_branch(overflows, ovf_panic_bb, cont_bb)
                        .unwrap();
                    self.builder.position_at_end(ovf_panic_bb);
                    self.emit_arith_panic(ovf_msg, span, unwind_bb)?;
                } else {
                    let _ = self
                        .builder
                        .build_conditional_branch(is_zero, zero_panic_bb, cont_bb)
                        .unwrap();
                }
                self.builder.position_at_end(zero_panic_bb);
                self.emit_arith_panic(zero_msg, span, unwind_bb)?;

                self.builder.position_at_end(cont_bb);
                let val = match (op, signed) {
                    ("div", true) => self.builder.build_int_signed_div(lhs, rhs, "div").unwrap(),
                    ("div", false) => self
                        .builder
                        .build_int_unsigned_div(lhs, rhs, "div")
                        .unwrap(),
                    (_, true) => self.builder.build_int_signed_rem(lhs, rhs, "rem").unwrap(),
                    (_, false) => self
                        .builder
                        .build_int_unsigned_rem(lhs, rhs, "rem")
                        .unwrap(),
                };
                val.as_basic_value_enum()
            }
            "shl" | "shr" => {
                let rhs = self
                    .eval_operand(body, locals, &args[1])?
                    .expect("checked arithmetic operand must have a value")
                    .into_int_value();
                // Panic when the amount reaches the bit width. The unsigned
                // comparison also rejects negative amounts of signed types.
                // The shift itself is emitted in the guarded continuation
                // block, where the amount is known in range.
                let limit = rhs.get_type().const_int(bits, false);
                let too_big = self
                    .builder
                    .build_int_compare(IntPredicate::UGE, rhs, limit, "shift_ovf")
                    .unwrap();
                let panic_bb = self.append_block_to_current_fn("shift_ovf_panic");
                let _ = self
                    .builder
                    .build_conditional_branch(too_big, panic_bb, cont_bb)
                    .unwrap();
                let direction = if op == "shl" { "left" } else { "right" };
                self.builder.position_at_end(panic_bb);
                self.emit_arith_panic(
                    &format!("attempt to shift {direction} with overflow"),
                    span,
                    unwind_bb,
                )?;

                self.builder.position_at_end(cont_bb);
                if op == "shl" {
                    self.builder
                        .build_left_shift(lhs, rhs, "shl")
                        .unwrap()
                        .as_basic_value_enum()
                } else {
                    self.builder
                        .build_right_shift(lhs, rhs, signed, "shr")
                        .unwrap()
                        .as_basic_value_enum()
                }
            }
            _ => {
                // Negation: only the minimum signed value overflows.
                let min = int_ty.const_int(1u64 << (bits - 1), false);
                let is_min = self
                    .builder
                    .build_int_compare(IntPredicate::EQ, lhs, min, "neg_min")
                    .unwrap();
                let panic_bb = self.append_block_to_current_fn("neg_ovf_panic");
                let _ = self
                    .builder
                    .build_conditional_branch(is_min, panic_bb, cont_bb)
                    .unwrap();
                self.builder.position_at_end(panic_bb);
                self.emit_arith_panic("attempt to negate with overflow", span, unwind_bb)?;

                self.builder.position_at_end(cont_bb);
                self.builder
                    .build_int_neg(lhs, "neg")
                    .unwrap()
                    .as_basic_value_enum()
            }
        };

        self.builder.position_at_end(cont_bb);
        self.store_place(destination, body, locals, result)?;
        let _ = self.builder.build_unconditional_branch(normal_bb).unwrap();
        Ok(true)
    }

    /// Emit a diverging call to the runtime panic entry point, honoring the
    /// surrounding call's unwind edge so cleanups run. The builder must be
    /// positioned in a dedicated panic block; the block ends `unreachable`.
    fn emit_arith_panic(
        &mut self,
        message: &str,
        span: crate::span::Span,
        unwind_bb: Option<BasicBlock<'llvm>>,
    ) -> CompileResult<()> {
        let msg = self.const_string_value(message);
        let file = self
            .gcx
            .dcx()
            .file_path(span.file)
            .map(|p| p.to_string_lossy().into_owned())
            .unwrap_or_else(|| "<unknown>".to_string());
        let file_val = self.const_string_value(&file);
        let line = self.usize_ty.const_int((span.start.line + 1) as u64, false);
        let column = self
            .usize_ty
            .const_int((span.start.offset + 1) as u64, false);
        let panic_fn = self.get_panic_unwind_at_fn();
        self.emit_source_typed_gc_stack_map(span, StackMapSiteKind::Panic);
        let _ = self.emit_call_maybe_unwind(
            CallTarget::Direct(panic_fn),
            &[msg, file_val, line.into(), column.into()],
            unwind_bb,
            "arith_panic",
        )?;
        let _ = self.builder.build_unreachable().unwrap();
        Ok(())
    }

    fn lower_cast(
        &mut self,
        from_ty: Ty<'gcx>,
        to_ty: Ty<'gcx>,
        value: BasicValueEnum<'llvm>,
    ) -> Option<BasicValueEnum<'llvm>> {
        let from_ty = self.mono_ty(from_ty);
        let to_ty = self.mono_ty(to_ty);
        if from_ty == to_ty {
            return Some(value);
        }

        // Integer-to-bool compares against zero (`2 as bool == true`) rather
        // than truncating to the low bit.
        if matches!(to_ty.kind(), TyKind::Bool) && self.int_type(from_ty).is_some() {
            let int_val = value.into_int_value();
            let zero = int_val.get_type().const_zero();
            return Some(
                self.builder
                    .build_int_compare(IntPredicate::NE, int_val, zero, "to_bool")
                    .unwrap()
                    .as_basic_value_enum(),
            );
        }

        if let (Some((_, from_signed)), Some((to_int, _))) =
            (self.int_type(from_ty), self.int_type(to_ty))
        {
            // Widening extends based on the *source* signedness (as in C/Rust/Go):
            // signed sources sign-extend, unsigned sources (incl. bool/rune) zero-extend.
            return Some(
                self.builder
                    .build_int_cast_sign_flag(
                        value.into_int_value(),
                        to_int,
                        from_signed,
                        "int_cast",
                    )
                    .unwrap()
                    .as_basic_value_enum(),
            );
        }

        if let (Some(_), Some(to_float)) = (self.int_type(from_ty), self.float_type(to_ty)) {
            let signed = is_signed(from_ty);
            return Some(
                if signed {
                    self.builder
                        .build_signed_int_to_float(value.into_int_value(), to_float, "itof")
                        .unwrap()
                } else {
                    self.builder
                        .build_unsigned_int_to_float(value.into_int_value(), to_float, "itof")
                        .unwrap()
                }
                .as_basic_value_enum(),
            );
        }

        if let (Some(_), Some((to_int, to_signed))) =
            (self.float_type(from_ty), self.int_type(to_ty))
        {
            return Some(
                if to_signed {
                    self.builder
                        .build_float_to_signed_int(value.into_float_value(), to_int, "ftoi")
                        .unwrap()
                } else {
                    self.builder
                        .build_float_to_unsigned_int(value.into_float_value(), to_int, "ftoi")
                        .unwrap()
                }
                .as_basic_value_enum(),
            );
        }

        if let (Some(_), Some(to_float)) = (self.float_type(from_ty), self.float_type(to_ty)) {
            let val = value.into_float_value();
            return Some(
                self.builder
                    .build_float_cast(val, to_float, "fcast")
                    .unwrap()
                    .as_basic_value_enum(),
            );
        }

        if matches!(to_ty.kind(), TyKind::Pointer(..) | TyKind::Reference(..)) {
            let ptr_ty = self.context.ptr_type(AddressSpace::default());
            let data = match value {
                BasicValueEnum::IntValue(int) => self
                    .builder
                    .build_int_to_ptr(int, ptr_ty, "inttoptr")
                    .unwrap(),
                _ => self.reference_data(value),
            };
            return Some(if matches!(to_ty.kind(), TyKind::Reference(..)) {
                if matches!(from_ty.kind(), TyKind::Reference(..)) {
                    value // A reference coercion preserves its existing control.
                } else {
                    self.lexical_reference(data) // Unsafe raw-to-reference conversion.
                }
            } else {
                data.into()
            });
        }
        if matches!(from_ty.kind(), TyKind::Pointer(..) | TyKind::Reference(..)) {
            if let Some((to_int, _)) = self.int_type(to_ty) {
                return Some(
                    self.builder
                        .build_ptr_to_int(self.reference_data(value), to_int, "ptrtoint")
                        .unwrap()
                        .into(),
                );
            }
        }

        None
    }

    /// Coerce a non-capturing closure to a function pointer.
    /// The shim passes the empty environment value required by the closure body.
    fn lower_closure_to_fn_pointer(
        &mut self,
        from_ty: Ty<'gcx>,
        to_ty: Ty<'gcx>,
    ) -> CompileResult<BasicValueEnum<'llvm>> {
        let TyKind::Closure {
            closure_def_id,
            captured_generics,
            ..
        } = from_ty.kind()
        else {
            panic!("ICE: closure to fn pointer cast on non-closure type");
        };

        let TyKind::FnPointer { inputs, output, .. } = to_ty.kind() else {
            panic!("ICE: closure to fn pointer cast to non-fn-pointer type");
        };

        let closure_args = if captured_generics.is_empty() {
            self.current_subst
        } else {
            captured_generics
        };

        // Generate a unique name for the shim
        let shim_name = format!(
            "{}_fn_shim",
            mangle_instance(self.gcx, Instance::item(closure_def_id, closure_args),)
        );

        // Check if we've already generated this shim
        if let Some(existing) = self.module.get_function(&shim_name) {
            return Ok(existing.as_global_value().as_pointer_value().into());
        }

        // Get the closure body function
        let closure_instance = Instance::item(closure_def_id, closure_args);
        let (closure_fn, closure_fn_abi) = self.instance_function_with_abi(closure_instance);

        // Build the shim function type (without self parameter).
        let shim_fn_abi = self.compute_fn_pointer_abi(inputs.as_slice(), output);
        let shim_fn_ty = self.lower_fn_abi(&shim_fn_abi);

        // Create the shim function
        let shim_fn = self
            .module
            .add_function(&shim_name, shim_fn_ty, Some(Linkage::Internal));
        // The borrowed environment is protected by the caller's map. Preserve
        // the bridge frame so collection inside the closure can reach it.
        self.preserve_diagnostic_frame(shim_fn);
        let entry_bb = self.context.append_basic_block(shim_fn, "entry");

        // Save current builder position
        let saved_bb = self.builder.get_insert_block();

        // Build the shim body
        self.builder.position_at_end(entry_bb);

        // A noncapturing closure receives an empty environment value. No
        // artificial reference or addressable temporary is needed.
        let mut call_args: Vec<BasicMetadataValueEnum> = Vec::new();
        let mut shim_param_index = 0u32;
        if matches!(closure_fn_abi.ret.mode, abi::PassMode::Indirect { .. }) {
            call_args.push(shim_fn.get_nth_param(shim_param_index).unwrap().into());
            shim_param_index += 1;
        }
        if !matches!(closure_fn_abi.args[0].mode, abi::PassMode::Ignore) {
            let empty = self
                .lower_ty(from_ty)
                .expect("closure environment")
                .const_zero();
            call_args.push(empty.into());
        }
        while shim_param_index < shim_fn.count_params() {
            call_args.push(shim_fn.get_nth_param(shim_param_index).unwrap().into());
            shim_param_index += 1;
        }

        // Call the closure body
        let call = self
            .builder
            .build_call(closure_fn, &call_args, "closure_call")
            .unwrap();

        // Return the result
        match closure_fn_abi.ret.mode {
            abi::PassMode::Ignore | abi::PassMode::Indirect { .. } => {
                self.builder.build_return(None).unwrap();
            }
            abi::PassMode::Direct => {
                if let Some(ret_val) = call.try_as_basic_value().basic() {
                    self.builder.build_return(Some(&ret_val)).unwrap();
                } else {
                    self.builder.build_return(None).unwrap();
                }
            }
        }

        // Restore builder position
        if let Some(bb) = saved_bb {
            self.builder.position_at_end(bb);
        }

        Ok(shim_fn.as_global_value().as_pointer_value().into())
    }

    fn build_existential_value(
        &self,
        ty: Ty<'gcx>,
        data_ptr: PointerValue<'llvm>,
        metadata_ptr: PointerValue<'llvm>,
        tables: &[PointerValue<'llvm>],
    ) -> BasicValueEnum<'llvm> {
        let Some(BasicTypeEnum::StructType(struct_ty)) = self.lower_ty(ty) else {
            return data_ptr.as_basic_value_enum();
        };

        let mut value = struct_ty.get_undef();
        value = self
            .builder
            .build_insert_value(value, data_ptr, 0, "exist_data")
            .unwrap()
            .into_struct_value();
        value = self
            .builder
            .build_insert_value(value, metadata_ptr, 1, "exist_meta")
            .unwrap()
            .into_struct_value();
        for (index, table) in tables.iter().enumerate() {
            value = self
                .builder
                .build_insert_value(
                    value,
                    (*table).as_basic_value_enum(),
                    (index + 2) as u32,
                    "exist_table",
                )
                .unwrap()
                .into_struct_value();
        }

        value.as_basic_value_enum()
    }

    fn lower_terminator(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        terminator: &mir::Terminator<'gcx>,
        blocks: &[inkwell::basic_block::BasicBlock<'llvm>],
    ) -> CompileResult<()> {
        match &terminator.kind {
            mir::TerminatorKind::Goto { target } => {
                let _ = self
                    .builder
                    .build_unconditional_branch(blocks[target.index()])
                    .unwrap();
            }
            mir::TerminatorKind::UnresolvedGoto => {
                unreachable!("unresolved terminator should be patched before codegen");
            }
            mir::TerminatorKind::SwitchInt {
                discr,
                targets,
                otherwise,
            } => {
                let Some(value) = self.eval_operand(body, locals, discr)? else {
                    let _ = self.builder.build_unreachable().unwrap();
                    return Ok(());
                };
                let discr_val = value.into_int_value();
                let default_bb = blocks[otherwise.index()];

                let cases: Vec<(inkwell::values::IntValue<'llvm>, _)> = targets
                    .iter()
                    .map(|(const_val, bb)| {
                        (
                            discr_val.get_type().const_int(*const_val as u64, false),
                            blocks[bb.index()],
                        )
                    })
                    .collect();
                let _ = self
                    .builder
                    .build_switch(discr_val, default_bb, &cases)
                    .unwrap();
            }
            mir::TerminatorKind::Return => {
                let fn_abi = self
                    .current_fn_abi
                    .as_ref()
                    .expect("current function ABI must be set");
                if matches!(fn_abi.ret.mode, abi::PassMode::Indirect { .. }) {
                    let _ = self.builder.build_return(None).unwrap();
                } else {
                    let ret_place = mir::Place {
                        local: body.return_local,
                        projection: vec![],
                    };
                    match self.load_place(body, locals, &ret_place) {
                        Some(val) => {
                            let _ = self.builder.build_return(Some(&val)).unwrap();
                        }
                        None => {
                            let _ = self.builder.build_return(None).unwrap();
                        }
                    }
                }
            }
            mir::TerminatorKind::ResumeUnwind => {
                let Some(eh_slot) = self.eh_slot else {
                    self.gcx.dcx().emit_error(
                        "resume_unwind without EH slot".into(),
                        Some(terminator.span),
                    );
                    return Err(crate::error::ReportedError);
                };
                let resume_val = self
                    .builder
                    .build_load(self.eh_landingpad_ty(), eh_slot, "eh_resume")
                    .unwrap();
                let _ = self.builder.build_resume(resume_val).unwrap();
            }
            mir::TerminatorKind::Unreachable => {
                let _ = self.builder.build_unreachable().unwrap();
            }
            mir::TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                unwind,
            } => {
                let call_effect = self.call_effect(func)?;
                let normal_bb = blocks[target.index()];
                let unwind_bb = match unwind {
                    mir::CallUnwindAction::Cleanup(bb) => Some(blocks[bb.index()]),
                    mir::CallUnwindAction::Terminate => None,
                };
                if self.try_lower_static_reference(
                    body,
                    locals,
                    func,
                    destination,
                    normal_bb,
                    unwind_bb,
                    terminator.span,
                )? {
                    return Ok(());
                }
                if self.try_lower_class_field_modify(
                    body,
                    locals,
                    func,
                    args,
                    destination,
                    normal_bb,
                    unwind_bb,
                )? {
                    return Ok(());
                }
                // Checked arithmetic needs the unwind edge for its panic path,
                // so it is intercepted before the generic intrinsic dispatch.
                if self.try_lower_checked_arith_call(
                    body,
                    locals,
                    terminator.span,
                    func,
                    args,
                    destination,
                    normal_bb,
                    unwind_bb,
                )? {
                    return Ok(());
                }
                if self.try_lower_intrinsic_call(body, locals, func, args, destination)? {
                    let _ = self.builder.build_unconditional_branch(normal_bb).unwrap();
                    return Ok(());
                }
                if self.try_lower_std_panic_call(
                    body,
                    locals,
                    terminator.span,
                    func,
                    args,
                    destination,
                    normal_bb,
                    unwind_bb,
                )? {
                    return Ok(());
                }
                let foreign_call = self.is_foreign_call(func);
                if self.is_blocking_foreign_call(func) {
                    let (callable, fn_abi) = self.lower_callable_with_abi(func);
                    self.lowering_foreign_args = true;
                    let lowered_args =
                        self.lower_call_args_with_fn_abi(body, locals, args, destination, &fn_abi);
                    self.lowering_foreign_args = false;
                    let lowered_args = lowered_args?;
                    self.emit_source_typed_gc_stack_map(
                        terminator.span,
                        StackMapSiteKind::Blocking,
                    );
                    // The call may block indefinitely, so the thread parks at a
                    // safepoint for its duration instead of stalling every
                    // collection; a collection scans the frozen stack above
                    // this frame's stack pointer.
                    self.emit_gc_blocking_enter();
                    let normal = self.append_block_to_current_fn("blocking_return");
                    let cleanup = self.append_block_to_current_fn("blocking_unwind");
                    let personality = self.eh_personality_fn();
                    self.builder
                        .get_insert_block()
                        .unwrap()
                        .get_parent()
                        .unwrap()
                        .set_personality_function(personality);
                    let call_site = self
                        .builder
                        .build_invoke(callable, &lowered_args, normal, cleanup, "blocking_call")
                        .unwrap();
                    self.install_native_string_call_attributes(&fn_abi, call_site);
                    self.builder.position_at_end(cleanup);
                    let landing = self
                        .builder
                        .build_landing_pad(
                            self.eh_landingpad_ty(),
                            personality,
                            &[],
                            true,
                            "blocking_exception",
                        )
                        .unwrap()
                        .into_struct_value();
                    self.emit_gc_blocking_transition(
                        "__rt__gc_exit_blocking",
                        "gc_blocking_unwind_exit",
                    );
                    if let Some(unwind) = unwind_bb {
                        self.builder
                            .build_store(self.eh_slot.expect("cleanup exception slot"), landing)
                            .unwrap();
                        self.builder.build_unconditional_branch(unwind).unwrap();
                    } else {
                        self.builder.build_resume(landing).unwrap();
                    }
                    self.builder.position_at_end(normal);
                    self.emit_gc_blocking_transition("__rt__gc_exit_blocking", "gc_blocking_exit");
                    self.store_call_result(body, locals, destination, &fn_abi, call_site)?;
                    let _ = self.builder.build_unconditional_branch(normal_bb).unwrap();
                    return Ok(());
                }
                let virtual_instance = self.virtual_instance_for_call(func);
                if let Some(instance) = virtual_instance.as_ref() {
                    self.lower_virtual_call(
                        body,
                        locals,
                        instance,
                        args,
                        destination,
                        unwind_bb,
                        (call_effect != mir::CallEffect::Direct).then_some(terminator.span),
                    )?;
                } else {
                    let (target, fn_abi) = self.lower_call_target(body, locals, func, args)?;
                    self.lowering_foreign_args = foreign_call;
                    let lowered_args =
                        self.lower_call_args_with_fn_abi(body, locals, args, destination, &fn_abi);
                    self.lowering_foreign_args = false;
                    let lowered_args = lowered_args?;
                    {
                        self.emit_source_typed_gc_stack_map(
                            terminator.span,
                            StackMapSiteKind::Call,
                        );
                    }
                    let call_site =
                        self.emit_call_maybe_unwind(target, &lowered_args, unwind_bb, "call")?;
                    self.install_native_string_call_attributes(&fn_abi, call_site);
                    self.store_call_result(body, locals, destination, &fn_abi, call_site)?;
                }
                let _ = self.builder.build_unconditional_branch(normal_bb).unwrap();
            }
            mir::TerminatorKind::Yield { .. } | mir::TerminatorKind::GeneratorYield { .. } => {
                unreachable!(
                    "Yield terminators must be lowered by the state machine transform before codegen"
                );
            }
        }
        Ok(())
    }

    fn emit_gc_blocking_enter(&self) {
        let ptr_ty = self.context.ptr_type(AddressSpace::default());
        let stacksave = Intrinsic::find("llvm.stacksave")
            .expect("LLVM stacksave intrinsic")
            .get_declaration(&self.module, &[ptr_ty.into()])
            .expect("declare stacksave");
        let sp = self
            .builder
            .build_call(stacksave, &[], "gc_blocking_sp")
            .unwrap()
            .try_as_basic_value()
            .basic()
            .expect("stacksave returns a pointer");
        let symbol = "__rt__gc_enter_blocking_at";
        let function = self.module.get_function(symbol).unwrap_or_else(|| {
            let fn_ty = self.context.void_type().fn_type(&[ptr_ty.into()], false);
            self.module
                .add_function(symbol, fn_ty, Some(Linkage::External))
        });
        let _ = self
            .builder
            .build_call(function, &[sp.into()], "gc_blocking_enter")
            .unwrap();
    }

    fn emit_gc_blocking_transition(&self, symbol: &str, call_name: &str) {
        let function = self.module.get_function(symbol).unwrap_or_else(|| {
            let fn_ty = self.context.void_type().fn_type(&[], false);
            self.module
                .add_function(symbol, fn_ty, Some(Linkage::External))
        });
        let _ = self.builder.build_call(function, &[], call_name).unwrap();
    }

    fn is_foreign_call(&self, func: &mir::Operand<'gcx>) -> bool {
        let mir::Operand::Constant(constant) = func else {
            return false;
        };
        let mir::ConstantKind::Function(def_id, _, _) = constant.value else {
            return false;
        };
        matches!(
            self.gcx.get_signature(def_id).abi,
            Some(hir::Abi::C | hir::Abi::Blocking)
        )
    }

    /// A Taro function handed to foreign code may run on a thread the runtime
    /// never created, or after its caller parked for a blocking call. The shim
    /// registers or resumes the thread for the body and parks it again on
    /// return, so a foreign thread idling in C never stalls collection.
    fn foreign_callback_shim(&mut self, function: FunctionValue<'llvm>) -> FunctionValue<'llvm> {
        let name = format!("{}$foreign_entry", function.get_name().to_string_lossy());
        if let Some(existing) = self.module.get_function(&name) {
            return existing;
        }
        let shim = self
            .module
            .add_function(&name, function.get_type(), Some(Linkage::Internal));
        let param_count = function.count_params();
        let mut locations = vec![AttributeLoc::Return, AttributeLoc::Function];
        locations.extend((0..param_count).map(AttributeLoc::Param));
        for location in &locations {
            for attribute in function.attributes(*location) {
                shim.add_attribute(*location, attribute);
            }
        }
        let saved_block = self.builder.get_insert_block();
        let entry = self.context.append_basic_block(shim, "entry");
        self.builder.position_at_end(entry);
        let usize_ty = self.usize_ty;
        let enter = self
            .module
            .get_function("__rt__foreign_enter")
            .unwrap_or_else(|| {
                self.module.add_function(
                    "__rt__foreign_enter",
                    usize_ty.fn_type(&[], false),
                    Some(Linkage::External),
                )
            });
        let exit = self
            .module
            .get_function("__rt__foreign_exit")
            .unwrap_or_else(|| {
                self.module.add_function(
                    "__rt__foreign_exit",
                    self.context.void_type().fn_type(&[usize_ty.into()], false),
                    Some(Linkage::External),
                )
            });
        let token = self
            .builder
            .build_call(enter, &[], "foreign_token")
            .unwrap()
            .try_as_basic_value()
            .basic()
            .expect("foreign enter returns a token");
        let personality = self.eh_personality_fn();
        shim.set_personality_function(personality);
        let returned = self.context.append_basic_block(shim, "callback_return");
        let cleanup = self.context.append_basic_block(shim, "callback_unwind");
        let forwarded: Vec<_> = shim.get_param_iter().collect();
        let call = self
            .builder
            .build_invoke(function, &forwarded, returned, cleanup, "callback")
            .unwrap();
        for location in locations
            .iter()
            .filter(|location| **location != AttributeLoc::Function)
        {
            for attribute in function.attributes(*location) {
                call.add_attribute(*location, attribute);
            }
        }
        self.builder.position_at_end(cleanup);
        let landing = self
            .builder
            .build_landing_pad(
                self.eh_landingpad_ty(),
                personality,
                &[],
                true,
                "callback_exception",
            )
            .unwrap()
            .into_struct_value();
        self.builder.build_call(exit, &[token.into()], "").unwrap();
        let exception = self
            .builder
            .build_extract_value(landing, 0, "exception")
            .unwrap();
        let ptr_ty = self.context.ptr_type(AddressSpace::default());
        let abort = self
            .module
            .get_function("__rt__panic_abort_foreign")
            .unwrap_or_else(|| {
                self.module.add_function(
                    "__rt__panic_abort_foreign",
                    self.context.void_type().fn_type(&[ptr_ty.into()], false),
                    Some(Linkage::External),
                )
            });
        self.builder
            .build_call(abort, &[exception.into()], "")
            .unwrap();
        self.builder.build_unreachable().unwrap();
        self.builder.position_at_end(returned);
        let _ = self.builder.build_call(exit, &[token.into()], "").unwrap();
        match call.try_as_basic_value().basic() {
            Some(value) => self.builder.build_return(Some(&value)).unwrap(),
            None => self.builder.build_return(None).unwrap(),
        };
        if let Some(block) = saved_block {
            self.builder.position_at_end(block);
        }
        shim
    }

    fn is_blocking_foreign_call(&self, func: &mir::Operand<'gcx>) -> bool {
        let mir::Operand::Constant(constant) = func else {
            return false;
        };
        let mir::ConstantKind::Function(def_id, _, _) = constant.value else {
            return false;
        };
        self.gcx.get_signature(def_id).abi == Some(hir::Abi::Blocking)
    }

    fn try_lower_intrinsic_call(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        func: &Operand<'gcx>,
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
    ) -> CompileResult<bool> {
        let Operand::Constant(c) = func else {
            return Ok(false);
        };
        let mir::ConstantKind::Function(def_id, call_args, _) = c.value else {
            return Ok(false);
        };

        let Some(hir::Abi::Intrinsic) = self.gcx.get_signature(def_id).abi else {
            return Ok(false);
        };

        let ident = self.gcx.definition_ident(def_id);
        let name = self.gcx.symbol_text(ident.symbol);
        let name = name.as_ref();
        if self.try_lower_typed_math_intrinsic(name, body, locals, args, destination)? {
            return Ok(true);
        }
        if self.lower_intrinsic_integer_arith(body, locals, args, destination, name)? {
            return Ok(true);
        }
        if self.lower_intrinsic_integer_bit(body, locals, args, destination, name)? {
            return Ok(true);
        }
        match name {
            "__intrinsic_black_box" => {
                self.lower_intrinsic_black_box(body, locals, args, destination)?;
                Ok(true)
            }

            "__intrinsic_class_field_reference"
            | "__intrinsic_class_field_read"
            | "__intrinsic_class_field_write" => {
                self.lower_intrinsic_class_field(body, locals, args, destination, name, None)?;
                Ok(true)
            }

            "__intrinsic_ref_project" | "__intrinsic_ref_project_mut" => {
                self.lower_intrinsic_borrow_projection(body, locals, args, destination)?;
                Ok(true)
            }
            "__intrinsic_array_read_unchecked" => {
                self.lower_intrinsic_array_read(body, locals, args, destination)?;
                Ok(true)
            }
            "__intrinsic_array_write_unchecked" => {
                self.lower_intrinsic_array_write(body, locals, args)?;
                Ok(true)
            }
            "$gcAsyncFrameAllocate" => {
                self.lower_intrinsic_gc_frame_allocate(body, locals, call_args, args, destination)?;
                Ok(true)
            }
            "$gcSyncGeneratorFrameAllocate" => {
                self.lower_intrinsic_gc_sync_generator_frame_allocate(
                    body,
                    locals,
                    call_args,
                    args,
                    destination,
                )?;
                Ok(true)
            }
            "__intrinsic_gc_value_descriptor" => {
                let Some(crate::sema::models::GenericArgument::Type(ty)) = call_args.get(0) else {
                    unreachable!("GC value descriptor intrinsic has one type argument")
                };
                let descriptor = self.gc_value_descriptor_for(*ty);
                self.store_place(destination, body, locals, descriptor.into())?;
                Ok(true)
            }

            "__intrinsic_task_output_descriptor" => {
                self.lower_intrinsic_task_output_descriptor(
                    body,
                    locals,
                    call_args,
                    args,
                    destination,
                )?;
                Ok(true)
            }

            "__intrinsic_ref_to_ptr" => {
                self.lower_intrinsic_ref_to_ptr(body, locals, args, destination)?;
                Ok(true)
            }
            "__intrinsic_mut_ref_to_ptr" => {
                self.lower_intrinsic_ref_to_ptr(body, locals, args, destination)?;
                Ok(true)
            }
            "__intrinsic_ptr_to_u8" => {
                self.lower_intrinsic_ptr_to_u8(body, locals, args, destination)?;
                Ok(true)
            }
            "__intrinsic_ptr_to_u8_mut" => {
                self.lower_intrinsic_ptr_to_u8(body, locals, args, destination)?;
                Ok(true)
            }
            "__intrinsic_ptr_add" => {
                self.lower_intrinsic_ptr_add(body, locals, call_args, args, destination)?;
                Ok(true)
            }
            "__intrinsic_ptr_sub" => {
                self.lower_intrinsic_ptr_sub(body, locals, call_args, args, destination)?;
                Ok(true)
            }
            "__intrinsic_ptr_offset" => {
                self.lower_intrinsic_ptr_offset(body, locals, call_args, args, destination)?;
                Ok(true)
            }
            "__intrinsic_ptr_byte_add" => {
                self.lower_intrinsic_ptr_byte_add(body, locals, call_args, args, destination)?;
                Ok(true)
            }
            "__intrinsic_ptr_byte_sub" => {
                self.lower_intrinsic_ptr_byte_sub(body, locals, call_args, args, destination)?;
                Ok(true)
            }
            "__intrinsic_atomic_load"
            | "__intrinsic_atomic_store"
            | "__intrinsic_atomic_swap"
            | "__intrinsic_atomic_compare_exchange"
            | "__intrinsic_atomic_add" => {
                self.lower_intrinsic_atomic(name, body, locals, call_args, args, destination)?;
                Ok(true)
            }
            "__intrinsic_ptr_read" => {
                self.lower_intrinsic_ptr_read(body, locals, call_args, args, destination)?;
                Ok(true)
            }
            "__intrinsic_ptr_write" => {
                self.lower_intrinsic_ptr_write(body, locals, call_args, args, destination)?;
                Ok(true)
            }
            "__intrinsic_memcpy" => {
                self.lower_intrinsic_memcpy(body, locals, call_args, args)?;
                Ok(true)
            }
            "__intrinsic_memmove" => {
                self.lower_intrinsic_memmove(body, locals, call_args, args)?;
                Ok(true)
            }
            "__intrinsic_memset" => {
                self.lower_intrinsic_memset(body, locals, call_args, args)?;
                Ok(true)
            }
            "__intrinsic_size_of" => {
                self.lower_intrinsic_size_of(body, locals, call_args, args, destination)?;
                Ok(true)
            }
            "__intrinsic_align_of" => {
                self.lower_intrinsic_align_of(body, locals, call_args, args, destination)?;
                Ok(true)
            }
            "__intrinsic_maybe_uninit" => {
                self.lower_intrinsic_maybe_uninit(body, locals, destination)?;
                Ok(true)
            }
            "__intrinsic_sqrt" => {
                self.lower_intrinsic_unary_float(body, locals, args, destination, "sqrt")?;
                Ok(true)
            }
            "__intrinsic_sin" => {
                self.lower_intrinsic_unary_float(body, locals, args, destination, "sin")?;
                Ok(true)
            }
            "__intrinsic_cos" => {
                self.lower_intrinsic_unary_float(body, locals, args, destination, "cos")?;
                Ok(true)
            }
            "__intrinsic_tan" => {
                self.lower_libm_unary_float(
                    body,
                    locals,
                    args,
                    destination,
                    "__intrinsic_tan",
                    "tanf",
                    "tan",
                )?;
                Ok(true)
            }
            "__intrinsic_asin" => {
                self.lower_libm_unary_float(
                    body,
                    locals,
                    args,
                    destination,
                    "__intrinsic_asin",
                    "asinf",
                    "asin",
                )?;
                Ok(true)
            }
            "__intrinsic_acos" => {
                self.lower_libm_unary_float(
                    body,
                    locals,
                    args,
                    destination,
                    "__intrinsic_acos",
                    "acosf",
                    "acos",
                )?;
                Ok(true)
            }
            "__intrinsic_atan" => {
                self.lower_libm_unary_float(
                    body,
                    locals,
                    args,
                    destination,
                    "__intrinsic_atan",
                    "atanf",
                    "atan",
                )?;
                Ok(true)
            }
            "__intrinsic_sinh" => {
                self.lower_libm_unary_float(
                    body,
                    locals,
                    args,
                    destination,
                    "__intrinsic_sinh",
                    "sinhf",
                    "sinh",
                )?;
                Ok(true)
            }
            "__intrinsic_cosh" => {
                self.lower_libm_unary_float(
                    body,
                    locals,
                    args,
                    destination,
                    "__intrinsic_cosh",
                    "coshf",
                    "cosh",
                )?;
                Ok(true)
            }
            "__intrinsic_tanh" => {
                self.lower_libm_unary_float(
                    body,
                    locals,
                    args,
                    destination,
                    "__intrinsic_tanh",
                    "tanhf",
                    "tanh",
                )?;
                Ok(true)
            }
            "__intrinsic_exp" => {
                self.lower_intrinsic_unary_float(body, locals, args, destination, "exp")?;
                Ok(true)
            }
            "__intrinsic_exp2" => {
                self.lower_intrinsic_unary_float(body, locals, args, destination, "exp2")?;
                Ok(true)
            }
            "__intrinsic_log" => {
                self.lower_intrinsic_unary_float(body, locals, args, destination, "log")?;
                Ok(true)
            }
            "__intrinsic_log2" => {
                self.lower_intrinsic_unary_float(body, locals, args, destination, "log2")?;
                Ok(true)
            }
            "__intrinsic_log10" => {
                self.lower_intrinsic_unary_float(body, locals, args, destination, "log10")?;
                Ok(true)
            }
            "__intrinsic_fabs" => {
                self.lower_intrinsic_unary_float(body, locals, args, destination, "fabs")?;
                Ok(true)
            }
            "__intrinsic_floor" => {
                self.lower_intrinsic_unary_float(body, locals, args, destination, "floor")?;
                Ok(true)
            }
            "__intrinsic_ceil" => {
                self.lower_intrinsic_unary_float(body, locals, args, destination, "ceil")?;
                Ok(true)
            }
            "__intrinsic_trunc" => {
                self.lower_intrinsic_unary_float(body, locals, args, destination, "trunc")?;
                Ok(true)
            }
            "__intrinsic_rint" => {
                self.lower_intrinsic_unary_float(body, locals, args, destination, "rint")?;
                Ok(true)
            }
            "__intrinsic_nearbyint" => {
                self.lower_intrinsic_unary_float(body, locals, args, destination, "nearbyint")?;
                Ok(true)
            }
            "__intrinsic_round" => {
                self.lower_intrinsic_unary_float(body, locals, args, destination, "round")?;
                Ok(true)
            }
            "__intrinsic_roundeven" => {
                self.lower_intrinsic_unary_float(body, locals, args, destination, "roundeven")?;
                Ok(true)
            }
            "__intrinsic_pow" => {
                self.lower_intrinsic_binary_float(body, locals, args, destination, "pow")?;
                Ok(true)
            }
            "__intrinsic_powi" => {
                self.lower_intrinsic_powi(body, locals, args, destination)?;
                Ok(true)
            }
            "__intrinsic_copysign" => {
                self.lower_intrinsic_binary_float(body, locals, args, destination, "copysign")?;
                Ok(true)
            }
            "__intrinsic_fma" => {
                self.lower_intrinsic_ternary_float(body, locals, args, destination, "fma")?;
                Ok(true)
            }
            "__intrinsic_minimum" => {
                self.lower_intrinsic_binary_float(body, locals, args, destination, "minimum")?;
                Ok(true)
            }
            "__intrinsic_maximum" => {
                self.lower_intrinsic_binary_float(body, locals, args, destination, "maximum")?;
                Ok(true)
            }
            "__intrinsic_minimumnum" => {
                self.lower_intrinsic_binary_float(body, locals, args, destination, "minnum")?;
                Ok(true)
            }
            "__intrinsic_maximumnum" => {
                self.lower_intrinsic_binary_float(body, locals, args, destination, "maxnum")?;
                Ok(true)
            }
            "__intrinsic_string_from_parts" => {
                self.lower_intrinsic_string_from_parts(body, locals, args, destination)?;
                Ok(true)
            }

            "__intrinsic_string_slice" => {
                self.lower_intrinsic_string_slice(body, locals, args, destination)?;
                Ok(true)
            }
            "__intrinsic_string_data" => {
                self.lower_intrinsic_string_data(body, locals, args, destination)?;
                Ok(true)
            }
            "__intrinsic_string_len" => {
                self.lower_intrinsic_string_len(body, locals, args, destination)?;
                Ok(true)
            }
            "__intrinsic_env_argc" => {
                self.lower_intrinsic_env_argc(body, locals, destination)?;
                Ok(true)
            }
            "__intrinsic_env_argv" => {
                self.lower_intrinsic_env_argv(body, locals, destination)?;
                Ok(true)
            }
            "__intrinsic_rune_from_u32_unchecked" => {
                self.lower_intrinsic_rune_from_u32_unchecked(body, locals, args, destination)?;
                Ok(true)
            }
            _ => {
                self.gcx
                    .dcx()
                    .emit_error(format!("unknown intrinsic '{}'", name), None);
                Ok(true)
            }
        }
    }

    /// Materialize an arbitrary value across an opaque runtime call, then
    /// reload it. The runtime preserves the bytes, but LLVM cannot prove that
    /// through the separately compiled ABI boundary, which gives benchmark
    /// authors the identity-style optimization barrier they expect.
    fn lower_intrinsic_black_box(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
    ) -> CompileResult<()> {
        assert_eq!(
            args.len(),
            1,
            "__intrinsic_black_box requires exactly one argument"
        );
        let argument = &args[0];
        let Some(llvm_ty) = self.lower_ty(self.operand_ty(body, argument)) else {
            // Zero-sized values have no runtime representation to obscure.
            return Ok(());
        };
        let Some(value) = self.eval_operand(body, locals, argument)? else {
            return Ok(());
        };

        let temporary = self.build_entry_alloca(llvm_ty, "black_box_value");
        self.builder.build_store(temporary, value).unwrap();
        let pointer_ty = self.context.ptr_type(AddressSpace::default());
        let function_ty = self
            .context
            .void_type()
            .fn_type(&[pointer_ty.into(), self.usize_ty.into()], false);
        let black_box = self
            .module
            .get_function("__rt__black_box")
            .unwrap_or_else(|| {
                self.module
                    .add_function("__rt__black_box", function_ty, Some(Linkage::External))
            });
        let size = self.target_data.get_store_size(&llvm_ty);
        self.builder
            .build_call(
                black_box,
                &[
                    temporary.into(),
                    self.usize_ty.const_int(size, false).into(),
                ],
                "",
            )
            .unwrap();
        let result = self
            .builder
            .build_load(llvm_ty, temporary, "black_box_result")
            .unwrap();
        self.store_place(destination, body, locals, result)
    }

    fn try_lower_typed_math_intrinsic(
        &mut self,
        name: &str,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
    ) -> CompileResult<bool> {
        let Some(stem) = name.strip_prefix("__intrinsic_") else {
            return Ok(false);
        };

        if matches!(stem, "powi_f32_i32" | "powi_f64_i32") {
            self.lower_intrinsic_powi(body, locals, args, destination)?;
            return Ok(true);
        }

        let Some(op) = stem
            .strip_suffix("_f32")
            .or_else(|| stem.strip_suffix("_f64"))
        else {
            return Ok(false);
        };

        match op {
            "sqrt" | "sin" | "cos" | "exp" | "exp2" | "log" | "log2" | "log10" | "fabs"
            | "floor" | "ceil" | "trunc" | "rint" | "nearbyint" | "round" | "roundeven" => {
                self.lower_intrinsic_unary_float(body, locals, args, destination, op)?;
                Ok(true)
            }
            "tan" => {
                self.lower_libm_unary_float(body, locals, args, destination, name, "tanf", "tan")?;
                Ok(true)
            }
            "asin" => {
                self.lower_libm_unary_float(
                    body,
                    locals,
                    args,
                    destination,
                    name,
                    "asinf",
                    "asin",
                )?;
                Ok(true)
            }
            "acos" => {
                self.lower_libm_unary_float(
                    body,
                    locals,
                    args,
                    destination,
                    name,
                    "acosf",
                    "acos",
                )?;
                Ok(true)
            }
            "atan" => {
                self.lower_libm_unary_float(
                    body,
                    locals,
                    args,
                    destination,
                    name,
                    "atanf",
                    "atan",
                )?;
                Ok(true)
            }
            "sinh" => {
                self.lower_libm_unary_float(
                    body,
                    locals,
                    args,
                    destination,
                    name,
                    "sinhf",
                    "sinh",
                )?;
                Ok(true)
            }
            "cosh" => {
                self.lower_libm_unary_float(
                    body,
                    locals,
                    args,
                    destination,
                    name,
                    "coshf",
                    "cosh",
                )?;
                Ok(true)
            }
            "tanh" => {
                self.lower_libm_unary_float(
                    body,
                    locals,
                    args,
                    destination,
                    name,
                    "tanhf",
                    "tanh",
                )?;
                Ok(true)
            }
            "pow" | "copysign" | "minimum" | "maximum" => {
                self.lower_intrinsic_binary_float(body, locals, args, destination, op)?;
                Ok(true)
            }
            "minimumnum" => {
                self.lower_intrinsic_binary_float(body, locals, args, destination, "minnum")?;
                Ok(true)
            }
            "maximumnum" => {
                self.lower_intrinsic_binary_float(body, locals, args, destination, "maxnum")?;
                Ok(true)
            }
            "fma" => {
                self.lower_intrinsic_ternary_float(body, locals, args, destination, "fma")?;
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    fn lower_intrinsic_string_from_parts(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
    ) -> CompileResult<()> {
        let data = args
            .first()
            .expect("string_from_parts missing data pointer");
        let len = args.get(1).expect("string_from_parts missing length");

        let Some(data_val) = self.eval_operand(body, locals, data)? else {
            let _ = self.builder.build_unreachable().unwrap();
            return Ok(());
        };
        let Some(len_val) = self.eval_operand(body, locals, len)? else {
            let _ = self.builder.build_unreachable().unwrap();
            return Ok(());
        };

        let ptr_ty = self.context.ptr_type(AddressSpace::default());
        let data_ptr = match data_val {
            BasicValueEnum::PointerValue(ptr) => ptr,
            BasicValueEnum::IntValue(int_val) => self
                .builder
                .build_int_to_ptr(int_val, ptr_ty, "string_data_ptr")
                .unwrap(),
            _ => {
                self.gcx
                    .dcx()
                    .emit_error("string_from_parts expects a pointer for data".into(), None);
                return Ok(());
            }
        };

        let mut len_int = match len_val {
            BasicValueEnum::IntValue(int_val) => int_val,
            _ => {
                self.gcx
                    .dcx()
                    .emit_error("string_from_parts expects an integer length".into(), None);
                return Ok(());
            }
        };
        if len_int.get_type() != self.usize_ty {
            len_int = self
                .builder
                .build_int_cast(len_int, self.usize_ty, "string_len_cast")
                .unwrap();
        }

        let value = self.string_value_from_parts(data_ptr, len_int);
        self.store_place(destination, body, locals, value.into())
    }

    fn lower_intrinsic_string_data(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
    ) -> CompileResult<()> {
        let value = args.first().expect("string_data missing string value");
        let Some(value) = self.eval_operand(body, locals, value)? else {
            let _ = self.builder.build_unreachable().unwrap();
            return Ok(());
        };

        let struct_val = self
            .builder
            .build_load(
                string_header_ty(self.context, &self.target_data),
                self.reference_data(value),
                "borrowed_string_header",
            )
            .unwrap()
            .into_struct_value();

        let data = self
            .builder
            .build_extract_value(struct_val, 0, "string_data")
            .unwrap()
            .into_pointer_value();
        self.store_place(destination, body, locals, data.as_basic_value_enum())
    }

    fn lower_intrinsic_string_len(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
    ) -> CompileResult<()> {
        let value = args.first().expect("string_len missing string value");
        let Some(value) = self.eval_operand(body, locals, value)? else {
            let _ = self.builder.build_unreachable().unwrap();
            return Ok(());
        };

        let struct_val = self
            .builder
            .build_load(
                string_header_ty(self.context, &self.target_data),
                self.reference_data(value),
                "borrowed_string_header",
            )
            .unwrap()
            .into_struct_value();

        let len = self
            .builder
            .build_extract_value(struct_val, 1, "string_len")
            .unwrap()
            .into_int_value();
        self.store_place(destination, body, locals, len.as_basic_value_enum())
    }

    fn lower_intrinsic_env_argc(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        destination: &Place<'gcx>,
    ) -> CompileResult<()> {
        let argc_global = self.get_or_create_env_argc_global();
        let argc = self
            .builder
            .build_load(self.usize_ty, argc_global, "env_argc")
            .unwrap()
            .into_int_value();
        self.store_place(destination, body, locals, argc.as_basic_value_enum())
    }

    fn lower_intrinsic_env_argv(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        destination: &Place<'gcx>,
    ) -> CompileResult<()> {
        let ptr_ty = self.context.ptr_type(AddressSpace::default());
        let argv_global = self.get_or_create_env_argv_global();
        let argv = self
            .builder
            .build_load(ptr_ty, argv_global, "env_argv")
            .unwrap()
            .into_pointer_value();
        self.store_place(destination, body, locals, argv.as_basic_value_enum())
    }

    fn lower_intrinsic_rune_from_u32_unchecked(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
    ) -> CompileResult<()> {
        let value = args
            .first()
            .expect("rune_from_u32_unchecked missing source value");
        let Some(value) = self.eval_operand(body, locals, value)? else {
            let _ = self.builder.build_unreachable().unwrap();
            return Ok(());
        };

        let value = match value {
            BasicValueEnum::IntValue(int_val) => int_val,
            _ => {
                self.gcx.dcx().emit_error(
                    "rune_from_u32_unchecked expects an integer argument".into(),
                    None,
                );
                return Ok(());
            }
        };

        let rune = if value.get_type() == self.context.i32_type() {
            value
        } else {
            self.builder
                .build_int_cast(value, self.context.i32_type(), "rune_from_u32")
                .unwrap()
        };

        self.store_place(destination, body, locals, rune.as_basic_value_enum())
    }

    fn lower_intrinsic_unary_float(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
        intrinsic: &str,
    ) -> CompileResult<()> {
        let operand = args.first().expect("missing unary intrinsic operand");
        let Some(value) = self.eval_operand(body, locals, operand)? else {
            let _ = self.builder.build_unreachable().unwrap();
            return Ok(());
        };

        let float_val = match value {
            BasicValueEnum::FloatValue(float_val) => float_val,
            _ => {
                self.gcx.dcx().emit_error(
                    format!("'{}' expects a float or double argument", intrinsic),
                    None,
                );
                return Ok(());
            }
        };

        let ty = float_val.get_type();
        let Some(suffix) = self.float_intrinsic_suffix(ty) else {
            self.gcx.dcx().emit_error(
                format!("'{}' only supports float and double", intrinsic),
                None,
            );
            return Ok(());
        };

        let name = format!("llvm.{}.{}", intrinsic, suffix);
        let fn_ty = ty.fn_type(&[ty.into()], false);
        let callee = self.get_or_add_intrinsic_function(&name, fn_ty);
        let call = self
            .builder
            .build_call(callee, &[float_val.into()], "intrinsic_call")
            .unwrap();
        let Some(result) = call.try_as_basic_value().basic() else {
            self.gcx
                .dcx()
                .emit_error(format!("intrinsic '{}' returned void", name), None);
            return Ok(());
        };

        self.store_place(destination, body, locals, result)
    }

    fn lower_libm_unary_float(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
        intrinsic_name: &str,
        f32_symbol: &str,
        f64_symbol: &str,
    ) -> CompileResult<()> {
        let operand = args.first().expect("missing unary intrinsic operand");
        let Some(value) = self.eval_operand(body, locals, operand)? else {
            let _ = self.builder.build_unreachable().unwrap();
            return Ok(());
        };

        let float_val = match value {
            BasicValueEnum::FloatValue(float_val) => float_val,
            _ => {
                self.gcx.dcx().emit_error(
                    format!("'{}' expects a float or double argument", intrinsic_name),
                    None,
                );
                return Ok(());
            }
        };

        let ty = float_val.get_type();
        let (symbol, fn_ty) = match ty.get_bit_width() {
            32 => (f32_symbol, ty.fn_type(&[ty.into()], false)),
            64 => (f64_symbol, ty.fn_type(&[ty.into()], false)),
            _ => {
                self.gcx.dcx().emit_error(
                    format!("'{}' only supports float and double", intrinsic_name),
                    None,
                );
                return Ok(());
            }
        };

        let callee = self.get_or_add_external_function(symbol, fn_ty);
        let call = self
            .builder
            .build_call(callee, &[float_val.into()], "libm_call")
            .unwrap();
        let Some(result) = call.try_as_basic_value().basic() else {
            self.gcx
                .dcx()
                .emit_error(format!("libm function '{}' returned void", symbol), None);
            return Ok(());
        };

        self.store_place(destination, body, locals, result)
    }

    fn lower_intrinsic_binary_float(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
        intrinsic: &str,
    ) -> CompileResult<()> {
        let lhs = args.first().expect("missing binary intrinsic lhs");
        let rhs = args.get(1).expect("missing binary intrinsic rhs");

        let Some(lhs_val) = self.eval_operand(body, locals, lhs)? else {
            let _ = self.builder.build_unreachable().unwrap();
            return Ok(());
        };
        let Some(rhs_val) = self.eval_operand(body, locals, rhs)? else {
            let _ = self.builder.build_unreachable().unwrap();
            return Ok(());
        };

        let lhs_float = match lhs_val {
            BasicValueEnum::FloatValue(val) => val,
            _ => {
                self.gcx.dcx().emit_error(
                    format!("'{}' expects float or double arguments", intrinsic),
                    None,
                );
                return Ok(());
            }
        };
        let rhs_float = match rhs_val {
            BasicValueEnum::FloatValue(val) => val,
            _ => {
                self.gcx.dcx().emit_error(
                    format!("'{}' expects float or double arguments", intrinsic),
                    None,
                );
                return Ok(());
            }
        };

        let ty = lhs_float.get_type();
        if ty != rhs_float.get_type() {
            self.gcx.dcx().emit_error(
                format!("'{}' requires matching float types", intrinsic),
                None,
            );
            return Ok(());
        }
        let Some(suffix) = self.float_intrinsic_suffix(ty) else {
            self.gcx.dcx().emit_error(
                format!("'{}' only supports float and double", intrinsic),
                None,
            );
            return Ok(());
        };

        let name = format!("llvm.{}.{}", intrinsic, suffix);
        let fn_ty = ty.fn_type(&[ty.into(), ty.into()], false);
        let callee = self.get_or_add_intrinsic_function(&name, fn_ty);
        let call = self
            .builder
            .build_call(
                callee,
                &[lhs_float.into(), rhs_float.into()],
                "intrinsic_call",
            )
            .unwrap();
        let Some(result) = call.try_as_basic_value().basic() else {
            self.gcx
                .dcx()
                .emit_error(format!("intrinsic '{}' returned void", name), None);
            return Ok(());
        };

        self.store_place(destination, body, locals, result)
    }

    fn lower_intrinsic_ternary_float(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
        intrinsic: &str,
    ) -> CompileResult<()> {
        let x = args.first().expect("missing ternary intrinsic operand x");
        let y = args.get(1).expect("missing ternary intrinsic operand y");
        let z = args.get(2).expect("missing ternary intrinsic operand z");

        let Some(x_val) = self.eval_operand(body, locals, x)? else {
            let _ = self.builder.build_unreachable().unwrap();
            return Ok(());
        };
        let Some(y_val) = self.eval_operand(body, locals, y)? else {
            let _ = self.builder.build_unreachable().unwrap();
            return Ok(());
        };
        let Some(z_val) = self.eval_operand(body, locals, z)? else {
            let _ = self.builder.build_unreachable().unwrap();
            return Ok(());
        };

        let x_float = match x_val {
            BasicValueEnum::FloatValue(val) => val,
            _ => {
                self.gcx.dcx().emit_error(
                    format!("'{}' expects float or double arguments", intrinsic),
                    None,
                );
                return Ok(());
            }
        };
        let y_float = match y_val {
            BasicValueEnum::FloatValue(val) => val,
            _ => {
                self.gcx.dcx().emit_error(
                    format!("'{}' expects float or double arguments", intrinsic),
                    None,
                );
                return Ok(());
            }
        };
        let z_float = match z_val {
            BasicValueEnum::FloatValue(val) => val,
            _ => {
                self.gcx.dcx().emit_error(
                    format!("'{}' expects float or double arguments", intrinsic),
                    None,
                );
                return Ok(());
            }
        };

        let ty = x_float.get_type();
        if ty != y_float.get_type() || ty != z_float.get_type() {
            self.gcx.dcx().emit_error(
                format!("'{}' requires matching float types", intrinsic),
                None,
            );
            return Ok(());
        }
        let Some(suffix) = self.float_intrinsic_suffix(ty) else {
            self.gcx.dcx().emit_error(
                format!("'{}' only supports float and double", intrinsic),
                None,
            );
            return Ok(());
        };

        let name = format!("llvm.{}.{}", intrinsic, suffix);
        let fn_ty = ty.fn_type(&[ty.into(), ty.into(), ty.into()], false);
        let callee = self.get_or_add_intrinsic_function(&name, fn_ty);
        let call = self
            .builder
            .build_call(
                callee,
                &[x_float.into(), y_float.into(), z_float.into()],
                "intrinsic_call",
            )
            .unwrap();
        let Some(result) = call.try_as_basic_value().basic() else {
            self.gcx
                .dcx()
                .emit_error(format!("intrinsic '{}' returned void", name), None);
            return Ok(());
        };

        self.store_place(destination, body, locals, result)
    }

    fn lower_intrinsic_powi(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
    ) -> CompileResult<()> {
        let base = args.first().expect("missing powi base");
        let exponent = args.get(1).expect("missing powi exponent");

        let Some(base_val) = self.eval_operand(body, locals, base)? else {
            let _ = self.builder.build_unreachable().unwrap();
            return Ok(());
        };
        let Some(exponent_val) = self.eval_operand(body, locals, exponent)? else {
            let _ = self.builder.build_unreachable().unwrap();
            return Ok(());
        };

        let base_float = match base_val {
            BasicValueEnum::FloatValue(val) => val,
            _ => {
                self.gcx
                    .dcx()
                    .emit_error("'powi' expects a float or double base".into(), None);
                return Ok(());
            }
        };
        let exponent_int = match exponent_val {
            BasicValueEnum::IntValue(val) => val,
            _ => {
                self.gcx
                    .dcx()
                    .emit_error("'powi' expects an int32 exponent".into(), None);
                return Ok(());
            }
        };

        let ty = base_float.get_type();
        let Some(suffix) = self.float_intrinsic_suffix(ty) else {
            self.gcx
                .dcx()
                .emit_error("'powi' only supports float and double".into(), None);
            return Ok(());
        };
        let i32_ty = self.context.i32_type();
        let exponent_i32 = if exponent_int.get_type() == i32_ty {
            exponent_int
        } else {
            self.builder
                .build_int_cast(exponent_int, i32_ty, "powi_exp_cast")
                .unwrap()
        };

        let name = format!("llvm.powi.{}.i32", suffix);
        let fn_ty = ty.fn_type(&[ty.into(), i32_ty.into()], false);
        let callee = self.get_or_add_intrinsic_function(&name, fn_ty);
        let call = self
            .builder
            .build_call(
                callee,
                &[base_float.into(), exponent_i32.into()],
                "intrinsic_call",
            )
            .unwrap();
        let Some(result) = call.try_as_basic_value().basic() else {
            self.gcx
                .dcx()
                .emit_error(format!("intrinsic '{}' returned void", name), None);
            return Ok(());
        };

        self.store_place(destination, body, locals, result)
    }

    fn float_intrinsic_suffix(&self, ty: FloatType<'llvm>) -> Option<&'static str> {
        match ty.get_bit_width() {
            32 => Some("f32"),
            64 => Some("f64"),
            _ => None,
        }
    }

    fn get_or_add_intrinsic_function(
        &self,
        name: &str,
        fn_ty: FunctionType<'llvm>,
    ) -> FunctionValue<'llvm> {
        self.module
            .get_function(name)
            .unwrap_or_else(|| self.module.add_function(name, fn_ty, None))
    }

    fn get_or_add_external_function(
        &self,
        name: &str,
        fn_ty: FunctionType<'llvm>,
    ) -> FunctionValue<'llvm> {
        self.module.get_function(name).unwrap_or_else(|| {
            self.module
                .add_function(name, fn_ty, Some(Linkage::External))
        })
    }

    /// Intrinsic: __intrinsic_ptr_to_u8[T](*const T) -> *const uint8
    /// Intrinsic: __intrinsic_ptr_to_u8_mut[T](*mut T) -> *mut uint8
    /// Reinterprets a raw pointer as a byte pointer.
    fn lower_intrinsic_ptr_to_u8(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
    ) -> CompileResult<()> {
        let value = args.first().expect("ptr_to_u8 missing value");
        let Some(val) = self.eval_operand(body, locals, value)? else {
            let _ = self.builder.build_unreachable().unwrap();
            return Ok(());
        };

        let ptr_ty = self.context.ptr_type(AddressSpace::default());
        let ptr_val = match val {
            BasicValueEnum::PointerValue(ptr) => ptr,
            BasicValueEnum::IntValue(int_val) => self
                .builder
                .build_int_to_ptr(int_val, ptr_ty, "int_to_ptr")
                .unwrap(),
            _ => {
                self.gcx
                    .dcx()
                    .emit_error("ptr_to_u8 expects a pointer value".into(), None);
                return Ok(());
            }
        };

        let byte_ptr_ty = self.context.ptr_type(AddressSpace::default());
        let cast = self
            .builder
            .build_bit_cast(ptr_val, byte_ptr_ty, "ptr_u8")
            .unwrap();

        self.store_place(destination, body, locals, cast.into())
    }

    fn lower_call_target(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        function: &Operand<'gcx>,
        arguments: &[Operand<'gcx>],
    ) -> CompileResult<(CallTarget<'llvm>, abi::FnAbi<'gcx>)> {
        if let Some((callable, fn_abi)) = self.closure_callable(body, function) {
            return Ok((CallTarget::Direct(callable), fn_abi));
        }
        if matches!(
            self.operand_ty(body, function).kind(),
            TyKind::FnPointer { .. }
        ) && !matches!(function, Operand::Constant(_))
        {
            let (ty, pointer, fn_abi) =
                self.lower_fn_pointer_call_target(body, locals, function)?;
            return Ok((CallTarget::Indirect(ty, pointer), fn_abi));
        }
        if let Some(target) = self.lower_class_call_target(body, locals, function, arguments)? {
            return Ok(target);
        }
        let (callable, fn_abi) = self.lower_callable_with_abi(function);
        Ok((CallTarget::Direct(callable), fn_abi))
    }

    fn lower_callable_with_abi(
        &mut self,
        func: &Operand<'gcx>,
    ) -> (FunctionValue<'llvm>, abi::FnAbi<'gcx>) {
        if let Operand::Constant(c) = func {
            if let mir::ConstantKind::Function(def_id, args, _) = c.value {
                let instance = self.instance_for_call(def_id, args);
                if let InstanceKind::Virtual(_) = instance.kind() {
                    unreachable!(
                        "ICE: virtual call instance reached lower_callable_with_abi; \
                         Call terminators should route virtual calls through lower_virtual_call"
                    );
                }
                return self.instance_function_with_abi(instance);
            }
        }

        panic!("ICE: unable to lower callable operand: {:?}", func);
    }

    /// Resolve an instance to its LLVM function and ABI, declaring the
    /// function in this module on demand (e.g. a concrete function defined in
    /// another package that has not been referenced yet).
    fn instance_function_with_abi(
        &mut self,
        instance: Instance<'gcx>,
    ) -> (FunctionValue<'llvm>, abi::FnAbi<'gcx>) {
        let resolved_def_id = match instance.kind() {
            InstanceKind::Item(def_id) => def_id,
            InstanceKind::Virtual(_) => {
                unreachable!("ICE: virtual instance has no concrete function value");
            }
        };

        if let Some(function) = self.functions.get(&instance) {
            return function.clone();
        }

        let prev_subst = self.current_subst;
        self.current_subst = instance.args();
        let fn_abi = self.compute_instance_fn_abi(instance, resolved_def_id);
        let name = mangle_instance(self.gcx, instance);
        self.current_subst = prev_subst;

        if self.is_foreign_function(resolved_def_id) {
            let f = self.declare_foreign_function(resolved_def_id);
            self.insert_function_instance(instance, f, fn_abi.clone());
            return (f, fn_abi);
        }

        if !self.instance_has_mir_body(instance)
            && self.is_interface_requirement_method(resolved_def_id)
        {
            let prev_subst = self.current_subst;
            self.current_subst = instance.args();
            let fn_ty = self.lower_fn_abi(&fn_abi);
            self.current_subst = prev_subst;
            let f = self.declare_unreachable_stub(&name, fn_ty);
            self.insert_function_instance(instance, f, fn_abi.clone());
            return (f, fn_abi);
        }

        // Not declared yet (likely from another package); declare as external.
        let prev_subst = self.current_subst;
        self.current_subst = instance.args();
        let fn_ty = self.lower_fn_abi(&fn_abi);
        let f = self
            .module
            .add_function(&name, fn_ty, Some(Linkage::External));
        self.current_subst = prev_subst;
        self.insert_function_instance(instance, f, fn_abi.clone());
        (f, fn_abi)
    }

    fn is_interface_requirement_method(&self, def_id: hir::DefinitionID) -> bool {
        if self.gcx.definition_kind(def_id) != DefinitionKind::AssociatedFunction {
            return false;
        }
        let Some(parent) = self.gcx.definition_parent(def_id) else {
            return false;
        };
        self.gcx.definition_kind(parent) == DefinitionKind::Interface
    }

    fn declare_unreachable_stub(
        &mut self,
        name: &str,
        fn_ty: FunctionType<'llvm>,
    ) -> FunctionValue<'llvm> {
        if let Some(existing) = self.module.get_function(name) {
            return existing;
        }
        let f = self
            .module
            .add_function(name, fn_ty, Some(Linkage::Internal));
        let builder = self.context.create_builder();
        let entry = self.context.append_basic_block(f, "entry");
        builder.position_at_end(entry);
        let _ = builder.build_unreachable().unwrap();
        f
    }

    fn lower_fn_pointer_sig(
        &self,
        inputs: &'gcx [Ty<'gcx>],
        output: Ty<'gcx>,
    ) -> (FunctionType<'llvm>, abi::FnAbi<'gcx>) {
        let fn_abi = self.compute_fn_pointer_abi(inputs, output);
        (self.lower_fn_abi(&fn_abi), fn_abi)
    }

    fn lower_fn_pointer_call_target(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        func: &Operand<'gcx>,
    ) -> CompileResult<(FunctionType<'llvm>, PointerValue<'llvm>, abi::FnAbi<'gcx>)> {
        let TyKind::FnPointer {
            inputs,
            output,
            effects,
        } = self.operand_ty(body, func).kind()
        else {
            self.gcx
                .dcx()
                .emit_error("expected function pointer operand".into(), None);
            return Err(crate::error::ReportedError);
        };
        let Some(value) = self.eval_operand(body, locals, func)? else {
            self.gcx
                .dcx()
                .emit_error("expected function pointer value".into(), None);
            return Err(crate::error::ReportedError);
        };
        let BasicValueEnum::PointerValue(ptr) = value else {
            self.gcx
                .dcx()
                .emit_error("expected function pointer value".into(), None);
            return Err(crate::error::ReportedError);
        };

        let output = if effects.kind == crate::sema::models::ClosureKind::AsyncFn {
            self.gcx.async_handle_ty()
        } else {
            output
        };
        let (fn_ty, fn_abi) = self.lower_fn_pointer_sig(inputs.as_slice(), output);
        let fn_ptr_ty = self.context.ptr_type(AddressSpace::default());
        let cast_ptr = self
            .builder
            .build_bit_cast(ptr, fn_ptr_ty, "fn_ptr_cast")
            .unwrap()
            .into_pointer_value();
        Ok((fn_ty, cast_ptr, fn_abi))
    }

    /// Resolve the same concrete closure instance for ABI validation and calls.
    /// A closure's body is statically known even when its value is an operand.
    fn closure_instance(
        &self,
        body: &mir::Body<'gcx>,
        func: &Operand<'gcx>,
    ) -> Option<Instance<'gcx>> {
        if matches!(func, Operand::Constant(_)) {
            return None; // Constants handled by lower_callable.
        }
        let ty = self.mono_ty(body.operand_ty(self.gcx, func));

        // Check if it's a closure type
        let TyKind::Closure {
            closure_def_id,
            captured_generics,
            ..
        } = ty.kind()
        else {
            return None;
        };

        // Create an instance for the closure body function
        let closure_args = if captured_generics.is_empty() {
            self.current_subst
        } else {
            captured_generics
        };
        Some(Instance::item(closure_def_id, closure_args))
    }

    fn closure_callable(
        &mut self,
        body: &mir::Body<'gcx>,
        func: &Operand<'gcx>,
    ) -> Option<(FunctionValue<'llvm>, abi::FnAbi<'gcx>)> {
        let instance = self.closure_instance(body, func)?;
        Some(self.instance_function_with_abi(instance))
    }

    fn is_foreign_function(&self, id: hir::DefinitionID) -> bool {
        self.gcx.get_signature(id).abi.is_some()
    }

    fn declare_foreign_function(&mut self, id: hir::DefinitionID) -> FunctionValue<'llvm> {
        let sig = self.gcx.get_signature(id);
        let fn_abi =
            self.compute_instance_fn_abi(Instance::item(id, GenericArguments::empty()), id);
        let fn_ty = self.lower_fn_abi(&fn_abi);
        let ident = self.gcx.definition_ident(id);
        let name = self.gcx.symbol_text(ident.symbol);
        let name = name.as_ref();
        let input_types: Vec<_> = sig
            .inputs
            .iter()
            .filter(|input| self.lower_ty(input.ty).is_some())
            .map(|input| crate::sema::tycheck::utils::normalize_aliases(self.gcx, input.ty))
            .collect();
        let output_ty = crate::sema::tycheck::utils::normalize_aliases(self.gcx, sig.output);
        let native = self.get_or_add_external_function(name, fn_ty);
        assert_eq!(
            native.get_type(),
            fn_ty,
            "consistent foreign function signature"
        );
        let extensions = if matches!(
            sig.abi,
            Some(hir::Abi::C | hir::Abi::Runtime | hir::Abi::Blocking)
        ) {
            c_extensions::source(self.gcx, &input_types, output_ty)
        } else {
            vec![]
        };
        c_extensions::install_source(self.context, native, &extensions);
        for (location, attribute) in self.native_string_argument_attributes(&fn_abi) {
            native.add_attribute(location, attribute);
        }
        native
    }

    fn eval_operand(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &[LocalStorage<'llvm>],
        op: &mir::Operand<'gcx>,
    ) -> CompileResult<Option<BasicValueEnum<'llvm>>> {
        let value = match op {
            mir::Operand::Copy(place) | mir::Operand::CopyWith(place, _) => {
                self.load_place(body, locals, place)
            }
            mir::Operand::Constant(c) => self.lower_constant(c),
        };
        Ok(value)
    }

    fn load_place(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &[LocalStorage<'llvm>],
        place: &mir::Place<'gcx>,
    ) -> Option<BasicValueEnum<'llvm>> {
        let place_ty = self.place_ty(body, place);
        if place.projection.is_empty() {
            return match locals[place.local.index()] {
                LocalStorage::Value(Some(v)) => Some(v),
                LocalStorage::Value(None) => None,
                LocalStorage::Stack(ptr) => {
                    let ty = self.lower_ty(place_ty)?;
                    Some(self.builder.build_load(ty, ptr, "load").unwrap())
                }
            };
        }

        let ptr = self.project_place(place, body, locals);
        match ptr {
            Ok(ptr) => {
                let elem_ty = self.lower_ty(place_ty)?;
                if place_is_shared(place) {
                    Some(self.build_typed_shared_load(place_ty, elem_ty, ptr, "load"))
                } else {
                    Some(self.builder.build_load(elem_ty, ptr, "load").unwrap())
                }
            }
            Err(_) => None,
        }
    }

    fn store_local(
        &mut self,
        local: mir::LocalId,
        locals: &mut [LocalStorage<'llvm>],
        value: BasicValueEnum<'llvm>,
        body: &mir::Body<'gcx>,
    ) {
        match locals[local.index()] {
            LocalStorage::Value(_) => {
                locals[local.index()] = LocalStorage::Value(Some(value));
            }
            LocalStorage::Stack(ptr) => {
                if self.lower_ty(body.locals[local].ty).is_some() {
                    let _ = self.builder.build_store(ptr, value).unwrap();
                }
            }
        }
    }

    // Enum payload storage can contain pointers while its LLVM type consists
    // only of integer words. Use the source GC layout for this case; inspecting
    // the LLVM aggregate alone would miss managed pointers hidden by a tag.
    fn shared_words_hidden_by_layout(
        &mut self,
        source: Ty<'gcx>,
        ty: BasicTypeEnum<'llvm>,
    ) -> bool {
        let word = self.target_data.get_pointer_byte_size(None);
        !llvm_type_contains_pointer(ty)
            && !self.gc_layout_nodes_for_ty(source).is_empty()
            && !matches!(ty, BasicTypeEnum::StructType(s) if s.is_packed())
            && self.target_data.get_abi_alignment(&ty) >= word
            && self.target_data.get_store_size(&ty) % u64::from(word) == 0
    }

    fn build_typed_shared_load(
        &mut self,
        source: Ty<'gcx>,
        ty: BasicTypeEnum<'llvm>,
        pointer: PointerValue<'llvm>,
        name: &str,
    ) -> BasicValueEnum<'llvm> {
        if self.shared_words_hidden_by_layout(source, ty) {
            let temporary = self.build_entry_alloca(ty, "shared_tagged_copy");
            let size = self
                .usize_ty
                .const_int(self.target_data.get_store_size(&ty), false);
            self.build_element_atomic_memmove(
                temporary,
                pointer,
                size,
                self.target_data.get_pointer_byte_size(None),
            );
            self.builder.build_load(ty, temporary, name).unwrap()
        } else {
            self.build_shared_load(ty, pointer, name)
        }
    }

    fn build_typed_shared_store(
        &mut self,
        source: Ty<'gcx>,
        pointer: PointerValue<'llvm>,
        value: BasicValueEnum<'llvm>,
    ) {
        let ty = value.get_type();
        if self.shared_words_hidden_by_layout(source, ty) {
            let temporary = self.build_entry_alloca(ty, "shared_tagged_copy");
            self.builder.build_store(temporary, value).unwrap();
            let size = self
                .usize_ty
                .const_int(self.target_data.get_store_size(&ty), false);
            self.build_element_atomic_memmove(
                pointer,
                temporary,
                size,
                self.target_data.get_pointer_byte_size(None),
            );
        } else {
            self.build_shared_store(pointer, value);
        }
    }

    /// Load from memory another thread may write. Every pointer word is read
    /// with one unordered atomic access, so a racing reader observes some
    /// whole stored pointer and LLVM never splits or re-reads it. Other words
    /// stay plain: multiword values may tear under races, as in Go.
    pub(crate) fn build_shared_load(
        &self,
        ty: BasicTypeEnum<'llvm>,
        ptr: PointerValue<'llvm>,
        name: &str,
    ) -> BasicValueEnum<'llvm> {
        if !shared_access_splits(ty) {
            if self.copies_words_atomically(ty) {
                let temporary = self.build_entry_alloca(ty, "shared_copy");
                let size = self
                    .usize_ty
                    .const_int(self.target_data.get_store_size(&ty), false);
                let word = self.target_data.get_pointer_byte_size(None);
                self.build_element_atomic_memmove(temporary, ptr, size, word);
                return self.builder.build_load(ty, temporary, name).unwrap();
            }
            return self.builder.build_load(ty, ptr, name).unwrap();
        }
        match ty {
            BasicTypeEnum::PointerType(_) => {
                let value = self.builder.build_load(ty, ptr, name).unwrap();
                self.make_unordered(value.as_instruction_value());
                value
            }
            BasicTypeEnum::StructType(struct_ty) => {
                let mut aggregate = struct_ty.get_undef().as_aggregate_value_enum();
                for (index, field) in struct_ty.get_field_types().into_iter().enumerate() {
                    let field_ptr = self
                        .builder
                        .build_struct_gep(struct_ty, ptr, index as u32, "shared_field")
                        .unwrap();
                    let value = self.build_shared_load(field, field_ptr, name);
                    aggregate = self
                        .builder
                        .build_insert_value(aggregate, value, index as u32, "shared_insert")
                        .unwrap();
                }
                aggregate.into_struct_value().into()
            }
            BasicTypeEnum::ArrayType(array_ty) => {
                let element = array_ty.get_element_type();
                let mut aggregate = array_ty.get_undef().as_aggregate_value_enum();
                for index in 0..array_ty.len() {
                    let element_ptr = unsafe {
                        self.builder
                            .build_in_bounds_gep(
                                array_ty,
                                ptr,
                                &[
                                    self.usize_ty.const_zero(),
                                    self.usize_ty.const_int(index as u64, false),
                                ],
                                "shared_element",
                            )
                            .unwrap()
                    };
                    let value = self.build_shared_load(element, element_ptr, name);
                    aggregate = self
                        .builder
                        .build_insert_value(aggregate, value, index, "shared_insert")
                        .unwrap();
                }
                aggregate.into_array_value().into()
            }
            _ => self.builder.build_load(ty, ptr, name).unwrap(),
        }
    }

    /// Store to memory another thread may read; see `build_shared_load`.
    pub(crate) fn build_shared_store(
        &self,
        ptr: PointerValue<'llvm>,
        value: BasicValueEnum<'llvm>,
    ) {
        let ty = value.get_type();
        if !shared_access_splits(ty) {
            if self.copies_words_atomically(ty) {
                let temporary = self.build_entry_alloca(ty, "shared_copy");
                self.builder.build_store(temporary, value).unwrap();
                let size = self
                    .usize_ty
                    .const_int(self.target_data.get_store_size(&ty), false);
                let word = self.target_data.get_pointer_byte_size(None);
                self.build_element_atomic_memmove(ptr, temporary, size, word);
            } else {
                self.builder.build_store(ptr, value).unwrap();
            }
            return;
        }
        match ty {
            BasicTypeEnum::PointerType(_) => {
                let store = self.builder.build_store(ptr, value).unwrap();
                self.make_unordered(Some(store));
            }
            BasicTypeEnum::StructType(struct_ty) => {
                let aggregate = value.into_struct_value();
                for (index, _) in struct_ty.get_field_types().into_iter().enumerate() {
                    let field_ptr = self
                        .builder
                        .build_struct_gep(struct_ty, ptr, index as u32, "shared_field")
                        .unwrap();
                    let field = self
                        .builder
                        .build_extract_value(aggregate, index as u32, "shared_extract")
                        .unwrap();
                    self.build_shared_store(field_ptr, field);
                }
            }
            BasicTypeEnum::ArrayType(array_ty) => {
                let aggregate = value.into_array_value();
                for index in 0..array_ty.len() {
                    let element_ptr = unsafe {
                        self.builder
                            .build_in_bounds_gep(
                                array_ty,
                                ptr,
                                &[
                                    self.usize_ty.const_zero(),
                                    self.usize_ty.const_int(index as u64, false),
                                ],
                                "shared_element",
                            )
                            .unwrap()
                    };
                    let element = self
                        .builder
                        .build_extract_value(aggregate, index, "shared_extract")
                        .unwrap();
                    self.build_shared_store(element_ptr, element);
                }
            }
            _ => {
                self.builder.build_store(ptr, value).unwrap();
            }
        }
    }

    /// Pointer-bearing values too large to split move through a private
    /// temporary with a word-atomic copy.
    fn copies_words_atomically(&self, ty: BasicTypeEnum<'llvm>) -> bool {
        let word = self.target_data.get_pointer_byte_size(None);
        llvm_type_contains_pointer(ty)
            && !matches!(ty, BasicTypeEnum::StructType(s) if s.is_packed())
            && self.target_data.get_abi_alignment(&ty) >= word
            && self.target_data.get_store_size(&ty) % u64::from(word) == 0
    }

    fn build_element_atomic_memmove(
        &self,
        destination: PointerValue<'llvm>,
        source: PointerValue<'llvm>,
        count: IntValue<'llvm>,
        word: u32,
    ) {
        // Small typed copies need no runtime call. Load every source word
        // before storing any destination word, retaining memmove overlap
        // semantics. Atomic IR forbids LLVM from splitting pointer-sized words.
        if let Some(bytes) = count.get_zero_extended_constant()
            && bytes % u64::from(word) == 0
            && bytes / u64::from(word) <= MAX_SHARED_ACCESS_LEAVES as u64
        {
            let integer = self.usize_ty;
            debug_assert_eq!(integer.get_bit_width(), word * 8);
            let mut values = Vec::new();
            for offset in (0..bytes).step_by(word as usize) {
                let address = unsafe {
                    self.builder
                        .build_in_bounds_gep(
                            self.context.i8_type(),
                            source,
                            &[self.usize_ty.const_int(offset, false)],
                            "atomic_copy_source",
                        )
                        .unwrap()
                };
                let value = self
                    .builder
                    .build_load(integer, address, "atomic_copy_word")
                    .unwrap();
                self.make_unordered(value.as_instruction_value());
                values.push(value);
            }
            for (index, value) in values.into_iter().enumerate() {
                let address = unsafe {
                    self.builder
                        .build_in_bounds_gep(
                            self.context.i8_type(),
                            destination,
                            &[self
                                .usize_ty
                                .const_int(index as u64 * u64::from(word), false)],
                            "atomic_copy_destination",
                        )
                        .unwrap()
                };
                self.make_unordered(Some(self.builder.build_store(address, value).unwrap()));
            }
            return;
        }
        let ptr_ty = self.context.ptr_type(AddressSpace::default());
        let intrinsic = Intrinsic::find("llvm.memmove.element.unordered.atomic")
            .expect("element-atomic memmove intrinsic");
        let function = intrinsic
            .get_declaration(
                &self.module,
                &[ptr_ty.into(), ptr_ty.into(), self.usize_ty.into()],
            )
            .expect("element-atomic memmove declaration");
        let call = self
            .builder
            .build_call(
                function,
                &[
                    destination.into(),
                    source.into(),
                    count.into(),
                    self.context
                        .i32_type()
                        .const_int(u64::from(word), false)
                        .into(),
                ],
                "",
            )
            .unwrap();
        let align = self
            .context
            .create_enum_attribute(Attribute::get_named_enum_kind_id("align"), u64::from(word));
        call.add_attribute(AttributeLoc::Param(0), align);
        call.add_attribute(AttributeLoc::Param(1), align);
    }

    fn make_unordered(&self, instruction: Option<inkwell::values::InstructionValue<'llvm>>) {
        let instruction = instruction.expect("shared pointer access is an instruction");
        instruction
            .set_atomic_ordering(inkwell::AtomicOrdering::Unordered)
            .expect("pointer access accepts unordered atomicity");
        instruction
            .set_alignment(self.target_data.get_pointer_byte_size(None))
            .expect("pointer access alignment");
    }

    fn store_place(
        &mut self,
        place: &mir::Place<'gcx>,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        value: BasicValueEnum<'llvm>,
    ) -> CompileResult<()> {
        if place.projection.is_empty() {
            self.store_local(place.local, locals, value, body);
            return Ok(());
        }

        let ptr = self.project_place(place, body, locals)?;
        if place_is_shared(place) {
            let ty = self.place_ty(body, place);
            self.build_typed_shared_store(ty, ptr, value);
        } else {
            self.builder.build_store(ptr, value).unwrap();
        }
        Ok(())
    }

    fn project_place(
        &mut self,
        place: &mir::Place<'gcx>,
        body: &mir::Body<'gcx>,
        locals: &[LocalStorage<'llvm>],
    ) -> CompileResult<PointerValue<'llvm>> {
        let mut ptr = match locals[place.local.index()] {
            LocalStorage::Stack(p) => p,
            LocalStorage::Value(Some(val)) => self.reference_data(val),
            LocalStorage::Value(None) => {
                panic!(
                    "use of uninitialized local {} while projecting a place with {} projection elems of type {}",
                    place.local.index(),
                    place.projection.len(),
                    self.place_ty(body, place).format(self.gcx)
                );
            }
        };

        // If the pointer comes from a stack slot, we need to load it to follow
        // the deref. Once we have a pointer value, further derefs load from
        // that address if needed.
        let mut ptr_is_storage = matches!(locals[place.local.index()], LocalStorage::Stack(_));
        let mut ty = body.locals[place.local].ty;
        // Storage reached through a pointer may be shared with other threads.
        let mut through_pointer = false;

        for elem in &place.projection {
            ty = self.mono_ty(ty);
            match elem {
                mir::PlaceElem::Deref => {
                    if ptr_is_storage {
                        let pointer_ty = self.lower_ty(ty).expect("reference/pointer layout");
                        let loaded = if through_pointer {
                            self.build_shared_load(pointer_ty, ptr, "deref")
                        } else {
                            self.builder.build_load(pointer_ty, ptr, "deref").unwrap()
                        };
                        ptr = self.reference_data(loaded);
                    }
                    ptr_is_storage = true;
                    through_pointer = true;
                    if let TyKind::Pointer(inner, _) | TyKind::Reference(inner) = ty.kind() {
                        ty = inner;
                    }
                }
                mir::PlaceElem::Field(idx, field_ty) => {
                    // Compute pointer to the requested field.
                    let struct_field_index = {
                        let mono_base_ty = self.mono_ty(ty);
                        match mono_base_ty.kind() {
                            TyKind::Adt(def, adt_args)
                                if def.kind == crate::sema::models::AdtKind::Struct =>
                            {
                                let defn = self.gcx.get_struct_definition(def.id);
                                let layout = struct_field_layout(
                                    self.context,
                                    self.gcx,
                                    &self.target_data,
                                    def.id,
                                    adt_args,
                                    GenericArguments::empty(),
                                    defn.repr,
                                );
                                *layout
                                    .logical_to_physical
                                    .get(idx.index())
                                    .unwrap_or_else(|| {
                                        panic!(
                                            "struct field index {} out of bounds for {}",
                                            idx.index(),
                                            mono_base_ty.format(self.gcx)
                                        )
                                    })
                            }
                            _ => idx.index() as u32,
                        }
                    };
                    let agg_ty = self.lower_ty(ty).expect("aggregate type lowered");
                    match agg_ty {
                        BasicTypeEnum::StructType(st) => {
                            let gep = match self.builder.build_struct_gep(
                                st,
                                ptr,
                                struct_field_index,
                                "field_ptr",
                            ) {
                                Ok(gep) => gep,
                                Err(err) => {
                                    panic!(
                                        "field projection GEP failed: index={}, base_ty={}, field_ty={}, place={:?}, err={:?}",
                                        struct_field_index,
                                        ty.format(self.gcx),
                                        field_ty.format(self.gcx),
                                        place,
                                        err
                                    );
                                }
                            };
                            ptr = gep;
                        }
                        BasicTypeEnum::ArrayType(arr_ty) => {
                            let zero = self.usize_ty.const_zero();
                            let idx_val = self.usize_ty.const_int(idx.index() as u64, false);
                            let gep = unsafe {
                                self.builder
                                    .build_gep(arr_ty, ptr, &[zero, idx_val], "array_elem_ptr")
                                    .unwrap()
                            };
                            ptr = gep;
                        }
                        _ => {
                            panic!(
                                "field projection on non-aggregate type {}",
                                ty.format(self.gcx)
                            )
                        }
                    }

                    ptr_is_storage = true;
                    ty = *field_ty;
                }
                mir::PlaceElem::VariantDowncast { name: _, index } => {
                    let (def, adt_args) = match ty.kind() {
                        TyKind::Adt(def, args)
                            if def.kind == crate::sema::models::AdtKind::Enum =>
                        {
                            (def, args)
                        }
                        _ => panic!("variant downcast on non-enum type {}", ty.format(self.gcx)),
                    };
                    let layout = self.enum_layout_for(def.id, adt_args);

                    let variant_ty = mir::enum_variant_tuple_ty(self.gcx, def.id, *index, adt_args);

                    if layout.npo.is_some() {
                        // NPO: the value IS the payload — no struct GEP needed.
                        // ptr already points to the niche-eligible value.
                        ptr_is_storage = true;
                        ty = variant_ty;
                    } else {
                        let payload_ptr = if let Some(payload_index) = layout.payload_field_index {
                            let enum_ty = self.lower_ty(ty).expect("enum");
                            let enum_struct = enum_ty.into_struct_type();
                            self.builder
                                .build_struct_gep(
                                    enum_struct,
                                    ptr,
                                    payload_index,
                                    "enum_payload_ptr",
                                )
                                .unwrap()
                        } else {
                            // Zero-sized enum payloads (e.g. Optional[()]) have no dedicated payload field.
                            // Reuse the enum base address as the variant payload base.
                            ptr
                        };

                        let _variant_struct = match self.lower_ty(variant_ty) {
                            Some(BasicTypeEnum::StructType(st)) => st,
                            None => self.context.struct_type(&[], false),
                            Some(other) => {
                                panic!("variant tuple lowered to non-struct {:?}", other);
                            }
                        };
                        let variant_ptr = self
                            .builder
                            .build_bit_cast(
                                payload_ptr,
                                self.context.ptr_type(AddressSpace::default()),
                                "enum_variant_ptr",
                            )
                            .unwrap()
                            .into_pointer_value();

                        ptr = variant_ptr;
                        ptr_is_storage = true;
                        ty = variant_ty;
                    }
                }
            }
        }

        Ok(ptr)
    }

    fn place_ty(&self, body: &mir::Body<'gcx>, place: &mir::Place<'gcx>) -> Ty<'gcx> {
        body.place_ty_with(self.gcx, place, |ty| self.mono_ty(ty))
    }

    fn lower_constant(&mut self, constant: &mir::Constant<'gcx>) -> Option<BasicValueEnum<'llvm>> {
        match &constant.value {
            mir::ConstantKind::Bool(b) => Some(
                self.context
                    .bool_type()
                    .const_int(*b as u64, false)
                    .as_basic_value_enum(),
            ),
            mir::ConstantKind::Rune(r) => Some(
                self.context
                    .i32_type()
                    .const_int(*r as u64, false)
                    .as_basic_value_enum(),
            ),
            mir::ConstantKind::Bytes(value) => Some(
                value
                    .with_bytes(|b| self.context.const_string(b, false))
                    .as_basic_value_enum(),
            ),
            mir::ConstantKind::ConstArray(arr) => {
                self.lower_const_array_with_ty(constant.ty, *arr)
            }
            mir::ConstantKind::String(sym) => {
                let ptr = self.lower_string(*sym);
                let len = self
                    .usize_ty
                    .const_int(self.gcx.symbol_text(sym).len() as u64, false);
                let Some(ty) = self.lower_ty(constant.ty) else {
                    return None;
                };
                let string_ty = ty.into_struct_type();
                let value = self.string_constant_header(string_ty, ptr, len);
                Some(value.as_basic_value_enum())
            }
            mir::ConstantKind::Integer(i) => self
                .int_type(constant.ty)
                .map(|(ty, _)| ty.const_int(*i, false).as_basic_value_enum()),
            mir::ConstantKind::Float(f) => self
                .float_type(constant.ty)
                .map(|ty| ty.const_float(*f).as_basic_value_enum()),
            mir::ConstantKind::Unit if matches!(constant.ty.kind(), TyKind::Pointer(..)) => Some(
                self.context
                    .ptr_type(AddressSpace::default())
                    .const_null()
                    .as_basic_value_enum(),
            ),
            mir::ConstantKind::Unit => None,
            mir::ConstantKind::InterfaceConstant(id, args) => {
                let interface = InterfaceReference {
                    id: self
                        .gcx
                        .definition_parent(*id)
                        .expect("interface constant owner"),
                    arguments: self.resolve_generic_args(*args),
                    bindings: &[],
                };
                let value = self
                    .conformance_witness(interface)
                    .and_then(|witness| witness.constant_witnesses.get(id).copied())
                    .and_then(|implementation| self.gcx.try_get_const(implementation));
                let Some(ConstKind::Value(value)) = value.map(|constant| constant.kind) else {
                    self.gcx.dcx().emit_error(
                        format!(
                            "cannot resolve interface constant '{}'",
                            self.gcx.symbol_text(self.gcx.definition_ident(*id).symbol)
                        ),
                        None,
                    );
                    return None;
                };
                self.lower_const_value_with_ty(self.mono_ty(constant.ty), value)
            }
            mir::ConstantKind::ConstParam(param) => {
                let konst = crate::sema::models::Const {
                    ty: constant.ty,
                    kind: ConstKind::Param(*param),
                };
                let instantiated = self.substitute_const_current(konst);
                let ConstKind::Value(value) = instantiated.kind else {
                    self.gcx
                        .dcx()
                        .emit_error("const parameter could not be resolved".into(), None);
                    return None;
                };
                self.lower_const_value_with_ty(constant.ty, value)
            }
            mir::ConstantKind::Function(def_id, args, _) => {
                let instance = self.instance_for_call(*def_id, *args);
                if let InstanceKind::Virtual(_) = instance.kind() {
                    unreachable!(
                        "ICE: virtual interface method reached lower_constant as a function value; \
                         frontend/typecheck should reject or lower this before codegen"
                    );
                }
                // Declare on demand: concrete functions from other packages are
                // not pre-declared, and returning None here would silently drop
                // the function pointer value.
                let (f, _) = self.instance_function_with_abi(instance);
                let f = if self.lowering_foreign_args {
                    self.foreign_callback_shim(f)
                } else {
                    f
                };
                Some(f.as_global_value().as_pointer_value().as_basic_value_enum())
            }
            mir::ConstantKind::GlobalVariableAddress(def_id) => {
                Some(self.global_variable_address(*def_id).as_basic_value_enum())
            }
        }
    }

    fn lower_string(&mut self, sym: Symbol) -> PointerValue<'llvm> {
        if let Some(ptr) = self.strings.get(&sym) {
            return *ptr;
        }
        let sym_text = self.gcx.symbol_text(&sym);
        let string_const = self
            .context
            .const_string(sym_text.as_ref().as_bytes(), true);
        let global = self.module.add_global(
            string_const.get_type(),
            None,
            &format!("__str_{}", self.strings.len()),
        );
        global.set_initializer(&string_const);
        global.set_constant(true);
        global.set_linkage(Linkage::Private);
        global.set_unnamed_addr(true);
        let ptr = global
            .as_pointer_value()
            .const_cast(self.context.ptr_type(AddressSpace::default()));
        let _ = self.strings.insert(sym, ptr);
        ptr
    }

    fn operand_ty(&self, body: &mir::Body<'gcx>, operand: &mir::Operand<'gcx>) -> Ty<'gcx> {
        let ty = match operand {
            mir::Operand::Copy(place) | mir::Operand::CopyWith(place, _) => {
                self.place_ty(body, place)
            }
            mir::Operand::Constant(c) => match c.value {
                mir::ConstantKind::Function(definition, call_args, function_ty) => {
                    // Function-item types live in the callee's generic index
                    // space, while their recorded call arguments can still
                    // refer to the caller's parameters. Resolve those two
                    // layers in that order. Applying the caller substitution
                    // directly can otherwise map a callee type parameter onto
                    // an unrelated caller const parameter at the same index.
                    let template = self.gcx.try_get_type(definition).unwrap_or(function_ty);
                    instantiate_ty_with_args(self.gcx, template, call_args)
                }
                _ => c.ty,
            },
        };

        self.substitute_ty_current(ty)
    }

    fn int_type(&self, ty: Ty<'gcx>) -> Option<(IntType<'llvm>, bool)> {
        match self.mono_ty(ty).kind() {
            TyKind::Bool => Some((self.context.bool_type(), false)),
            TyKind::Rune => Some((self.context.i32_type(), false)),
            TyKind::Int(i) => Some((int_from_kind(self.context, &self.target_data, i), true)),
            TyKind::UInt(u) => Some((uint_from_kind(self.context, &self.target_data, u), false)),
            _ => None,
        }
    }

    fn float_type(&self, ty: Ty<'gcx>) -> Option<FloatType<'llvm>> {
        match self.mono_ty(ty).kind() {
            TyKind::Float(FloatTy::F32) => Some(self.context.f32_type()),
            TyKind::Float(FloatTy::F64) => Some(self.context.f64_type()),
            _ => None,
        }
    }
}

#[derive(Clone, Copy)]
struct NpoLayout {
    /// The variant index that carries the payload (the non-unit variant).
    payload_variant: usize,
    /// The variant index that is the unit/none variant (represented as null).
    null_variant: usize,
}

#[derive(Clone, Copy)]
struct EnumLayout<'llvm> {
    discr_ty: IntType<'llvm>,
    discr_size: u64,
    payload_size: u64,
    /// Alignment the widest variant needs. The payload is lowered as an array of
    /// integers this wide so the enum's LLVM type carries the requirement — a
    /// byte array would report alignment 1 and let a contained pointer land at
    /// any address.
    payload_align: u64,
    payload_offset: u64,
    payload_field_index: Option<u32>,
    /// When set, this enum uses null-pointer optimization: no discriminant tag,
    /// the null bit pattern represents the unit variant.
    npo: Option<NpoLayout>,
}

/// The narrowest integer type that can hold every variant index of an enum.
///
/// The tag is written and read only through `EnumLayout::discr_ty`, and the
/// discriminant *value* stays `usize` in MIR, so reads widen back to it.
fn discriminant_int_type<'llvm>(context: &'llvm Context, variant_count: usize) -> IntType<'llvm> {
    // An empty enum has no variants to tell apart, but still needs a tag type.
    let largest = variant_count.saturating_sub(1) as u64;
    if largest <= u8::MAX as u64 {
        context.i8_type()
    } else if largest <= u16::MAX as u64 {
        context.i16_type()
    } else if largest <= u32::MAX as u64 {
        context.i32_type()
    } else {
        context.i64_type()
    }
}

fn enum_payload_is_scalar(payload_size: u64, payload_align: u64) -> bool {
    payload_size > 0 && payload_size <= payload_align && payload_align <= 8
}

/// The payload blob of an enum, with element width carrying the alignment the
/// widest variant needs. A single element remains scalar so small enums can
/// use the existing scalar-aggregate ABI rather than the array fallback.
///
/// Sized up to a whole number of elements; the excess is padding a correctly
/// aligned struct would have anyway.
fn enum_payload_field_ty<'llvm>(
    context: &'llvm Context,
    payload_size: u64,
    payload_align: u64,
) -> BasicTypeEnum<'llvm> {
    let (element, width) = match payload_align {
        a if a >= 8 => (context.i64_type(), 8u64),
        4 => (context.i32_type(), 4u64),
        2 => (context.i16_type(), 2u64),
        _ => (context.i8_type(), 1u64),
    };
    let count = payload_size.div_ceil(width);
    if enum_payload_is_scalar(payload_size, payload_align) {
        return element.into();
    }
    element
        .array_type(u32::try_from(count).expect("enum payload fits u32"))
        .into()
}

fn align_up(value: u64, align: u64) -> u64 {
    if align == 0 {
        return value;
    }
    let rem = value % align;
    if rem == 0 {
        value
    } else {
        value + (align - rem)
    }
}

/// Returns `true` when `ty` is guaranteed to never have an all-zero bit pattern,
/// making it eligible for null-pointer optimization in enums.
fn is_niche_eligible_ty<'gcx>(gcx: Gcx<'gcx>, ty: Ty<'gcx>, subst: GenericArguments<'gcx>) -> bool {
    let ty = if subst.is_empty() {
        ty
    } else {
        instantiate_ty_with_args(gcx, ty, subst)
    };
    let ty = crate::sema::tycheck::utils::normalize_aliases(gcx, ty);
    // For a borrow carrier, only its data word is the niche discriminator;
    // the permission word is preserved by payload construction/projection.
    matches!(ty.kind(), TyKind::Reference(..) | TyKind::FnPointer { .. }) || gcx.is_class_type(ty)
}

fn enum_layout<'llvm, 'gcx>(
    context: &'llvm Context,
    gcx: Gcx<'gcx>,
    target_data: &TargetData,
    def_id: hir::DefinitionID,
    adt_args: GenericArguments<'gcx>,
    subst: GenericArguments<'gcx>,
) -> EnumLayout<'llvm> {
    let def = gcx.get_enum_definition(def_id);
    // The tag only has to distinguish the variants, so it is sized to the
    // smallest integer that can hold the largest index. A pointer-sized tag
    // costs eight bytes on every enum, which for a payload-free one — the
    // common `Kind`-style enum — is the whole value.
    let discr_ty = discriminant_int_type(context, def.variants.len());
    let discr_size = target_data.get_store_size(&discr_ty);
    let mut payload_size = 0u64;
    let mut payload_align = 1u64;

    for variant in def.variants.iter() {
        let (size, align) = match variant.kind {
            crate::sema::models::EnumVariantKind::Unit => (0u64, 1u64),
            crate::sema::models::EnumVariantKind::Tuple(fields)
            | crate::sema::models::EnumVariantKind::Struct(fields) => {
                if fields.is_empty() {
                    (0u64, 1u64)
                } else {
                    let struct_ty =
                        enum_variant_struct_ty(context, gcx, target_data, fields, adt_args, subst);
                    let size = target_data.get_store_size(&struct_ty);
                    let align = target_data.get_abi_alignment(&struct_ty) as u64;
                    (size, align)
                }
            }
        };
        payload_size = payload_size.max(size);
        payload_align = payload_align.max(align);
    }

    let payload_offset = align_up(discr_size, payload_align);
    let payload_field_index = (payload_size > 0).then_some(1);

    // Detect null-pointer optimization eligibility:
    // Exactly 2 variants, one unit and one with a single niche-eligible field.
    let npo = if def.variants.len() == 2 {
        let mut unit_idx = None;
        let mut payload_idx = None;

        for (i, variant) in def.variants.iter().enumerate() {
            match variant.kind {
                crate::sema::models::EnumVariantKind::Unit => {
                    unit_idx = Some(i);
                }
                crate::sema::models::EnumVariantKind::Tuple(fields)
                | crate::sema::models::EnumVariantKind::Struct(fields)
                    if fields.is_empty() =>
                {
                    unit_idx = Some(i);
                }
                crate::sema::models::EnumVariantKind::Tuple(fields)
                | crate::sema::models::EnumVariantKind::Struct(fields)
                    if fields.len() == 1 =>
                {
                    let field_ty = instantiate_ty_with_args(gcx, fields[0].ty, adt_args);
                    if is_niche_eligible_ty(gcx, field_ty, subst) {
                        payload_idx = Some(i);
                    }
                }
                _ => {}
            }
        }

        match (unit_idx, payload_idx) {
            (Some(null_variant), Some(payload_variant)) if null_variant != payload_variant => {
                Some(NpoLayout {
                    payload_variant,
                    null_variant,
                })
            }
            _ => None,
        }
    } else {
        None
    };

    EnumLayout {
        discr_ty,
        discr_size,
        payload_align,
        payload_size,
        payload_offset,
        payload_field_index,
        npo,
    }
}

fn enum_variant_struct_ty<'llvm, 'gcx>(
    context: &'llvm Context,
    gcx: GlobalContext<'gcx>,
    target_data: &TargetData,
    fields: &[crate::sema::models::EnumVariantField<'gcx>],
    adt_args: GenericArguments<'gcx>,
    subst: GenericArguments<'gcx>,
) -> StructType<'llvm> {
    let field_tys: Vec<BasicTypeEnum<'llvm>> = fields
        .iter()
        .map(|field| {
            // Substitute field type with ADT's generic args.
            // Preserve field index positions for zero-sized fields (e.g. `()` payloads).
            let resolved = instantiate_ty_with_args(gcx, field.ty, adt_args);
            lower_type(context, gcx, target_data, resolved, subst)
                .unwrap_or_else(|| context.i8_type().array_type(0).into())
        })
        .collect();
    context.struct_type(&field_tys, false)
}

#[derive(Debug, Clone)]
struct StructFieldLayout {
    physical_to_logical: Vec<usize>,
    logical_to_physical: Vec<u32>,
}

fn packed_field_order(entries: &[(usize, u32, u64)]) -> Vec<usize> {
    let mut entries = entries.to_vec();
    entries.sort_by(|lhs, rhs| {
        rhs.1
            .cmp(&lhs.1)
            .then_with(|| rhs.2.cmp(&lhs.2))
            .then_with(|| lhs.0.cmp(&rhs.0))
    });
    entries
        .into_iter()
        .map(|(logical_index, _, _)| logical_index)
        .collect()
}

fn logical_to_physical_map(physical_to_logical: &[usize]) -> Vec<u32> {
    let mut logical_to_physical = vec![0_u32; physical_to_logical.len()];
    for (physical_index, logical_index) in physical_to_logical.iter().enumerate() {
        logical_to_physical[*logical_index] =
            u32::try_from(physical_index).expect("field index fits in u32");
    }
    logical_to_physical
}

fn struct_field_layout<'llvm, 'gcx>(
    context: &'llvm Context,
    gcx: GlobalContext<'gcx>,
    target_data: &TargetData,
    def_id: hir::DefinitionID,
    adt_args: GenericArguments<'gcx>,
    subst: GenericArguments<'gcx>,
    repr: StructRepr,
) -> StructFieldLayout {
    let field_count = gcx.get_struct_definition(def_id).fields.len();

    if field_count == 0 || repr == StructRepr::C {
        let physical_to_logical: Vec<usize> = (0..field_count).collect();
        let logical_to_physical: Vec<u32> = (0..field_count)
            .map(|idx| u32::try_from(idx).expect("field index fits in u32"))
            .collect();
        return StructFieldLayout {
            physical_to_logical,
            logical_to_physical,
        };
    }

    let defn = gcx.get_struct_definition(def_id);
    let mut entries: Vec<(usize, u32, u64)> = Vec::with_capacity(field_count);
    for (logical_index, field) in defn.fields.iter().enumerate() {
        let resolved = instantiate_ty_with_args(gcx, field.ty, adt_args);
        // Preserve slot positions for zero-sized fields when computing sort metrics.
        let llvm_ty = lower_type(context, gcx, target_data, resolved, subst)
            .unwrap_or_else(|| context.i8_type().array_type(0).into());
        let align = target_data.get_abi_alignment(&llvm_ty);
        let size = target_data.get_store_size(&llvm_ty);
        entries.push((logical_index, align, size));
    }

    // Stable deterministic packing heuristic for repr(Taro):
    // larger alignment first, then larger size, then source order.
    let physical_to_logical = packed_field_order(&entries);
    let logical_to_physical = logical_to_physical_map(&physical_to_logical);

    StructFieldLayout {
        physical_to_logical,
        logical_to_physical,
    }
}

#[cfg(test)]
fn build_byte_offset_ptr<'llvm>(
    context: &'llvm Context,
    builder: &Builder<'llvm>,
    usize_ty: IntType<'llvm>,
    base: PointerValue<'llvm>,
    offset: u64,
    name: &str,
) -> PointerValue<'llvm> {
    // A zero-offset GEP is semantically just its base pointer. Emitting the
    // redundant instruction also prevents mem2reg from recognizing an alloca
    // as promotable before InstCombine canonicalizes the GEP.
    if offset == 0 {
        return base;
    }

    let offset = usize_ty.const_int(offset, false);
    unsafe {
        builder
            .build_gep(context.i8_type(), base, &[offset], name)
            .unwrap()
    }
}

#[cfg(test)]
mod struct_layout_tests {
    use super::{
        AARCH64_INDIRECT_ARG_THRESHOLD_BYTES, AARCH64_INDIRECT_RETURN_THRESHOLD_BYTES,
        LlvmOptimizationPipeline, NON_AARCH64_INDIRECT_ARG_THRESHOLD_BYTES,
        NON_AARCH64_INDIRECT_RETURN_THRESHOLD_BYTES, add_llvm_enum_function_attribute,
        add_llvm_enum_function_attribute_with_value, add_llvm_string_function_attribute,
        build_byte_offset_ptr, has_llvm_bitcode_magic, has_llvm_function_body,
        indirect_arg_threshold_for_triple, indirect_return_threshold_for_triple,
        llvm_inline_attribute_name, llvm_optimization_pipeline, logical_to_physical_map,
        packed_field_order, place_operand, target_is_aarch64, write_llvm_bitcode,
    };
    use crate::test_support::TempDir;
    use crate::{
        codegen::target::TargetLayout,
        compile::config::{BuildProfile, LtoMode, OptLevel, OptimizationMode},
        diagnostics::DiagCtx,
        hir::KnownAttribute,
        mir::{CopyModifiers, Operand, Place},
    };
    use inkwell::{AddressSpace, attributes::AttributeLoc, context::Context, module::Module};
    use std::{fs, path::PathBuf};

    #[test]
    fn enum_alignment_padding_is_not_a_value_field() {
        let mut source = String::from(
            r#"
enum Bytes { case empty; case pair(uint8, uint8) }
enum Halves { case empty; case pair(uint16, uint16) }
enum Words { case empty; case pair(uint32, uint32) }
enum Longs { case empty; case pair(uint64, uint64) }
enum References { case empty; case pair(&int32, &int32) }
enum Mixed { case empty; case pair(uint8, uint64) }
enum Wide {
"#,
        );
        for index in 0..257 {
            source.push_str(&format!("case unit{index}\n"));
        }
        source.push_str("case pair(uint64, uint64)\n}\nfunc main() {}\n");
        crate::test_support::analyze_native_class_fixture(&source, &[], &[], |package, _, gcx| {
            let context = Context::create();
            for specification in [
                "e-p:64:64-i64:64-n32:64-S128",
                "e-p:32:32-i64:32-f64:32-n8:16:32-S128",
            ] {
                let data = inkwell::targets::TargetData::create(specification);
                for declaration in &package.root.declarations {
                    if !matches!(declaration.kind, crate::hir::DeclarationKind::Enum(_)) {
                        continue;
                    }
                    let ty = gcx.get_type(declaration.id);
                    let crate::sema::models::TyKind::Adt(definition, args) = ty.kind() else {
                        continue;
                    };
                    if definition.kind != crate::sema::models::AdtKind::Enum {
                        continue;
                    }
                    let layout = super::enum_layout(
                        &context,
                        gcx,
                        &data,
                        definition.id,
                        args,
                        crate::sema::models::GenericArguments::empty(),
                    );
                    let lowered = super::lower_type(
                        &context,
                        gcx,
                        &data,
                        ty,
                        crate::sema::models::GenericArguments::empty(),
                    )
                    .unwrap()
                    .into_struct_type();
                    assert_eq!(
                        lowered.count_fields(),
                        2,
                        "alignment padding must not become copied SSA bytes: {lowered:?}"
                    );
                    assert_eq!(layout.payload_field_index, Some(1));
                    assert_eq!(
                        data.offset_of_element(&lowered, 1),
                        Some(layout.payload_offset)
                    );
                    assert_eq!(
                        u64::from(data.get_abi_alignment(&lowered)),
                        layout.payload_align
                    );
                    assert_eq!(
                        data.get_store_size(&lowered),
                        super::align_up(
                            layout.payload_offset + layout.payload_size,
                            layout.payload_align
                        )
                    );
                    assert!(
                        super::llvm_type_contains_array(lowered.into()),
                        "multiword payload keeps the existing array ABI classification"
                    );
                }
            }
        });
    }

    #[test]
    fn scalar_enum_payload_preserves_layout_without_array_abi() {
        let context = Context::create();
        let data = inkwell::targets::TargetData::create("e-p:64:64-i64:64-n32:64-S128");
        for width in [1, 2, 4, 8] {
            let payload = super::enum_payload_field_ty(&context, width, width);
            assert!(payload.is_int_type());
            let value = context.struct_type(&[context.i8_type().into(), payload], false);
            assert_eq!(data.offset_of_element(&value, 1), Some(width));
            assert_eq!(data.get_store_size(&value), width * 2);
            assert!(!super::llvm_type_contains_array(value.into()));
        }
        let large = super::enum_payload_field_ty(&context, 16, 8);
        assert!(super::llvm_type_contains_array(large));
        assert_eq!(data.get_store_size(&large), 16);
    }

    #[test]
    fn bitcode_round_trip_preserves_target_identity() {
        let diagnostics = DiagCtx::new(PathBuf::from("."));
        let layout = TargetLayout::new(&diagnostics, None, BuildProfile::Release)
            .unwrap_or_else(|_| panic!("host target layout should initialize"));
        let context = Context::create();
        let module = context.create_module("bitcode-round-trip");
        module.set_triple(&layout.triple());
        module.set_data_layout(&layout.data_layout());
        module.add_function("smoke", context.void_type().fn_type(&[], false), None);

        let root = TempDir::new("round-trip");
        let path = root.join("module.bc");
        write_llvm_bitcode(&module, &path).expect("bitcode write should succeed");
        let bytes = fs::read(&path).expect("bitcode should be readable");
        assert!(has_llvm_bitcode_magic(&bytes));

        let parsed_context = Context::create();
        let parsed = Module::parse_bitcode_from_path(&path, &parsed_context)
            .expect("emitted bitcode should parse");
        assert_eq!(parsed.get_triple(), layout.triple());
        assert_eq!(
            parsed.get_data_layout().as_str(),
            layout.data_layout().as_str()
        );
    }

    #[test]
    fn bitcode_writer_accepts_non_ascii_paths() {
        let context = Context::create();
        let module = context.create_module("non-ascii-bitcode-path");
        let root = TempDir::new("bitcode-unicode");
        let path = root.join("taro-bitcode-雪.bc");

        write_llvm_bitcode(&module, &path).expect("non-ASCII path should be supported");
        assert!(fs::metadata(&path).expect("bitcode metadata").len() > 0);
    }

    #[test]
    fn packed_field_order_sorts_by_align_then_size_then_source_index() {
        // (logical_index, abi_align, store_size)
        let entries = vec![(0, 4, 4), (1, 8, 1), (2, 8, 8), (3, 4, 8), (4, 8, 8)];

        let order = packed_field_order(&entries);
        assert_eq!(order, vec![2, 4, 1, 3, 0]);
    }

    #[test]
    fn packed_field_order_is_deterministic_for_ties() {
        let entries = vec![(0, 8, 8), (1, 8, 8), (2, 8, 8)];
        let order = packed_field_order(&entries);
        assert_eq!(order, vec![0, 1, 2]);
    }

    #[test]
    fn logical_to_physical_mapping_is_inverse_of_physical_order() {
        let physical_to_logical = vec![2, 0, 1];
        let logical_to_physical = logical_to_physical_map(&physical_to_logical);
        assert_eq!(logical_to_physical, vec![1, 2, 0]);
    }

    #[test]
    fn aarch64_detection_accepts_common_apple_spellings() {
        assert!(target_is_aarch64("aarch64-unknown-linux-gnu"));
        assert!(target_is_aarch64("arm64-apple-darwin"));
        assert!(target_is_aarch64("arm64e-apple-darwin"));
        assert!(!target_is_aarch64("x86_64-apple-darwin"));
    }

    #[test]
    fn indirect_return_threshold_tracks_target_family() {
        assert_eq!(
            indirect_return_threshold_for_triple("arm64e-apple-darwin"),
            AARCH64_INDIRECT_RETURN_THRESHOLD_BYTES
        );
        assert_eq!(
            indirect_return_threshold_for_triple("x86_64-unknown-linux-gnu"),
            NON_AARCH64_INDIRECT_RETURN_THRESHOLD_BYTES
        );
    }

    #[test]
    fn indirect_argument_threshold_tracks_target_family() {
        assert_eq!(
            indirect_arg_threshold_for_triple("arm64e-apple-darwin"),
            AARCH64_INDIRECT_ARG_THRESHOLD_BYTES
        );
        assert_eq!(
            indirect_arg_threshold_for_triple("x86_64-unknown-linux-gnu"),
            NON_AARCH64_INDIRECT_ARG_THRESHOLD_BYTES
        );
    }

    #[test]
    fn large_aggregate_copy_source_accepts_plain_and_initializing_copies() {
        let place = Place::return_place();
        let operands = [
            Operand::Copy(place.clone()),
            Operand::CopyWith(place.clone(), CopyModifiers { init: false }),
        ];

        for operand in &operands {
            assert_eq!(place_operand(operand), Some(&place));
        }
    }

    #[test]
    fn llvm_pass_pipeline_preserves_baseline_and_maps_explicit_levels() {
        assert_eq!(
            llvm_optimization_pipeline(
                BuildProfile::Debug,
                OptimizationMode::Baseline,
                LtoMode::Off,
            ),
            LlvmOptimizationPipeline::Function("mem2reg")
        );
        assert_eq!(
            llvm_optimization_pipeline(
                BuildProfile::Release,
                OptimizationMode::Baseline,
                LtoMode::Off,
            ),
            LlvmOptimizationPipeline::Function("mem2reg,instcombine,reassociate,gvn,simplifycfg")
        );
        assert_eq!(
            llvm_optimization_pipeline(
                BuildProfile::Debug,
                OptimizationMode::Level(OptLevel::O0),
                LtoMode::Off,
            ),
            LlvmOptimizationPipeline::Function("mem2reg")
        );
        assert_eq!(
            llvm_optimization_pipeline(
                BuildProfile::Debug,
                OptimizationMode::Level(OptLevel::O2),
                LtoMode::Off,
            ),
            LlvmOptimizationPipeline::Module("default<O2>")
        );
        assert_eq!(
            llvm_optimization_pipeline(
                BuildProfile::Release,
                OptimizationMode::Level(OptLevel::Oz),
                LtoMode::Off,
            ),
            LlvmOptimizationPipeline::Module("default<Oz>")
        );
        assert_eq!(
            llvm_optimization_pipeline(
                BuildProfile::Release,
                OptimizationMode::Level(OptLevel::O2),
                LtoMode::Full,
            ),
            LlvmOptimizationPipeline::Module("lto-pre-link<O2>")
        );
        assert_eq!(
            llvm_optimization_pipeline(
                BuildProfile::Release,
                OptimizationMode::Level(OptLevel::O2),
                LtoMode::Thin,
            ),
            LlvmOptimizationPipeline::Module("thinlto-pre-link<O2>")
        );
        assert_eq!(
            llvm_optimization_pipeline(
                BuildProfile::Debug,
                OptimizationMode::Baseline,
                LtoMode::Thin,
            ),
            LlvmOptimizationPipeline::Module("function(mem2reg),thinlto-pre-link<O0>")
        );
    }

    #[test]
    fn source_inline_contracts_map_to_llvm_attributes() {
        assert_eq!(
            llvm_inline_attribute_name([KnownAttribute::Inline]),
            Some("inlinehint")
        );
        assert_eq!(
            llvm_inline_attribute_name([KnownAttribute::NoInline]),
            Some("noinline")
        );
        assert_eq!(llvm_inline_attribute_name([KnownAttribute::Test]), None);
    }

    #[test]
    fn collecting_frame_attributes_are_attached_to_functions() {
        let context = Context::create();
        let module = context.create_module("function-attributes");
        let function = module.add_function(
            "never_inline",
            context.void_type().fn_type(&[], false),
            None,
        );

        add_llvm_enum_function_attribute(&context, function, "noinline");
        add_llvm_string_function_attribute(&context, function, "disable-tail-calls", "true");
        add_llvm_enum_function_attribute_with_value(&context, function, "uwtable", 1);

        let kind_id = inkwell::attributes::Attribute::get_named_enum_kind_id("noinline");
        assert!(
            function
                .get_enum_attribute(AttributeLoc::Function, kind_id)
                .is_some()
        );
        let ir = module.print_to_string().to_string();
        assert!(ir.contains("noinline"));
        assert!(ir.contains("\"disable-tail-calls\"=\"true\""));
        assert!(ir.contains("uwtable(sync)"));
    }

    #[test]
    fn zero_byte_offset_reuses_the_base_pointer() {
        let context = Context::create();
        let module = context.create_module("zero-offset-pointer");
        let builder = context.create_builder();
        let pointer_ty = context.ptr_type(AddressSpace::default());
        let function = module.add_function(
            "test",
            context.void_type().fn_type(&[pointer_ty.into()], false),
            None,
        );
        let block = context.append_basic_block(function, "entry");
        builder.position_at_end(block);
        let base = function
            .get_first_param()
            .expect("pointer parameter")
            .into_pointer_value();

        let result = build_byte_offset_ptr(
            &context,
            &builder,
            context.i64_type(),
            base,
            0,
            "zero_offset",
        );
        builder.build_return(None).unwrap();

        assert_eq!(result, base);
        assert!(
            !module
                .print_to_string()
                .to_string()
                .contains("getelementptr")
        );
    }

    #[test]
    fn llvm_function_passes_skip_declarations() {
        let context = Context::create();
        let module = context.create_module("function-pass-candidates");
        let function_ty = context.void_type().fn_type(&[], false);
        let declaration = module.add_function("external", function_ty, None);
        let definition = module.add_function("defined", function_ty, None);
        let block = context.append_basic_block(definition, "entry");
        let builder = context.create_builder();
        builder.position_at_end(block);
        builder.build_return(None).unwrap();

        assert!(!has_llvm_function_body(declaration));
        assert!(has_llvm_function_body(definition));
    }
}

fn lower_type<'llvm, 'gcx>(
    context: &'llvm Context,
    gcx: GlobalContext<'gcx>,
    target_data: &TargetData,
    ty: Ty<'gcx>,
    subst: GenericArguments<'gcx>,
) -> Option<BasicTypeEnum<'llvm>> {
    // Resolve type parameters first
    let ty = if subst.is_empty() {
        ty
    } else {
        instantiate_ty_with_args(gcx, ty, subst)
    };
    // Normalize all aliases including projections
    let ty = crate::sema::tycheck::utils::normalize_post_monomorphization(gcx, ty);

    match ty.kind() {
        TyKind::Never => None,
        TyKind::Bool => Some(context.bool_type().into()),
        TyKind::Rune => Some(context.i32_type().into()),
        TyKind::String => Some(string_header_ty(context, target_data).into()),
        TyKind::Array { element, len } => {
            let Some(elem_ty) = lower_type(context, gcx, target_data, element, subst) else {
                return None;
            };
            let count = match len.kind {
                ConstKind::Value(ConstValue::Integer(i)) if i >= 0 => usize::try_from(i).ok()?,
                _ => return None,
            };
            Some(elem_ty.array_type(count as u32).into())
        }
        TyKind::Int(i) => Some(int_from_kind(context, target_data, i).into()),
        TyKind::UInt(u) => Some(uint_from_kind(context, target_data, u).into()),
        TyKind::Float(f) => Some(match f {
            FloatTy::F32 => context.f32_type().into(),
            FloatTy::F64 => context.f64_type().into(),
        }),
        TyKind::Adt(_, _) if gcx.is_class_type(ty) => Some(
            context
                .struct_type(&[context.ptr_type(AddressSpace::default()).into()], false)
                .into(),
        ),
        TyKind::Adt(def, adt_args) => match def.kind {
            crate::sema::models::AdtKind::Struct => {
                let defn = gcx.get_struct_definition(def.id);
                let layout = struct_field_layout(
                    context,
                    gcx,
                    target_data,
                    def.id,
                    adt_args,
                    subst,
                    defn.repr,
                );
                let logical_field_tys: Vec<BasicTypeEnum<'llvm>> = defn
                    .fields
                    .iter()
                    .map(|f| {
                        // Substitute field type with ADT's generic args
                        let resolved = instantiate_ty_with_args(gcx, f.ty, adt_args);
                        // Preserve field index positions for zero-sized fields.
                        lower_type(context, gcx, target_data, resolved, subst)
                            .unwrap_or_else(|| context.i8_type().array_type(0).into())
                    })
                    .collect();
                let reordered: Vec<BasicTypeEnum<'llvm>> = layout
                    .physical_to_logical
                    .iter()
                    .map(|logical_index| logical_field_tys[*logical_index])
                    .collect();
                Some(context.struct_type(&reordered, false).into())
            }
            crate::sema::models::AdtKind::Enum => {
                let layout = enum_layout(context, gcx, target_data, def.id, adt_args, subst);

                // Null-pointer optimization: represent as the payload type directly.
                if let Some(npo) = layout.npo {
                    let enum_def = gcx.get_enum_definition(def.id);
                    let variant = &enum_def.variants[npo.payload_variant];
                    let field_ty = match variant.kind {
                        crate::sema::models::EnumVariantKind::Tuple(fields)
                        | crate::sema::models::EnumVariantKind::Struct(fields) => {
                            instantiate_ty_with_args(gcx, fields[0].ty, adt_args)
                        }
                        _ => unreachable!("NPO payload variant must be a tuple"),
                    };
                    return lower_type(context, gcx, target_data, field_ty, subst);
                }

                let mut fields: Vec<BasicTypeEnum<'llvm>> = vec![layout.discr_ty.into()];

                if layout.payload_size == 0 {
                    return Some(context.struct_type(&fields, false).into());
                }

                // The payload's element type carries its alignment. LLVM's
                // natural struct padding preserves the offset without turning
                // padding bytes into SSA fields copied with every enum value.
                fields.push(enum_payload_field_ty(
                    context,
                    layout.payload_size,
                    layout.payload_align,
                ));
                Some(context.struct_type(&fields, false).into())
            }
        },
        TyKind::Reference(..) => Some(context.ptr_type(AddressSpace::default()).into()),
        TyKind::Pointer(..) => Some(
            context
                .ptr_type(AddressSpace::default())
                .as_basic_type_enum(),
        ),
        TyKind::Tuple(items) => {
            if items.is_empty() {
                None
            } else {
                let fields: Vec<BasicTypeEnum<'llvm>> = items
                    .iter()
                    .map(|t| {
                        // Preserve tuple field indices for zero-sized elements (e.g. `((), T)`).
                        lower_type(context, gcx, target_data, *t, subst)
                            .unwrap_or_else(|| context.i8_type().array_type(0).into())
                    })
                    .collect();
                Some(context.struct_type(&fields, false).into())
            }
        }
        TyKind::FnPointer { .. } => Some(
            context
                .ptr_type(AddressSpace::default())
                .as_basic_type_enum(),
        ),
        TyKind::BoxedExistential { interfaces } => {
            let ptr_ty = context.ptr_type(AddressSpace::default());
            let mut fields: Vec<BasicTypeEnum<'llvm>> = Vec::with_capacity(2 + interfaces.len());
            fields.push(ptr_ty.into());
            fields.push(ptr_ty.into());
            for _ in interfaces.iter() {
                fields.push(ptr_ty.into());
            }
            Some(context.struct_type(&fields, false).into())
        }
        TyKind::Parameter(_) => {
            // Should have been resolved by instantiate_ty_with_args above
            unreachable!(
                "ICE: unresolved type parameter in lower_type: {}",
                ty.format(gcx)
            )
        }
        TyKind::Alias { kind, def_id, args } => {
            let formatted = ty.format(gcx);
            let kind_str = match kind {
                crate::sema::models::AliasKind::Weak => "weak alias",
                crate::sema::models::AliasKind::Inherent => "inherent alias",
                crate::sema::models::AliasKind::Projection => "projection",
                crate::sema::models::AliasKind::Opaque => "opaque return",
            };
            unreachable!(
                "ICE: unnormalized {} in codegen: {}\n\
                 This should have been normalized by normalize_post_monomorphization.\n\
                 def_id: {:?}, args: {:?}",
                kind_str, formatted, def_id, args
            )
        }
        TyKind::Closure {
            closure_def_id,
            captured_generics,
            ..
        } => {
            // Closure is represented as its environment struct
            // Get the captures and build a struct type for them
            if let Some(captures) = gcx.get_closure_captures(closure_def_id) {
                if captures.captures.is_empty() {
                    // Empty closure - zero-sized struct (empty struct in LLVM)
                    Some(context.struct_type(&[], false).into())
                } else {
                    // Build struct from capture field types
                    let fields: Vec<BasicTypeEnum<'llvm>> = captures
                        .captures
                        .iter()
                        .filter_map(|cap| {
                            let resolved = instantiate_ty_with_args(
                                gcx,
                                cap.storage_ty(gcx, captured_generics),
                                subst,
                            );
                            lower_type(context, gcx, target_data, resolved, subst)
                        })
                        .collect();
                    Some(context.struct_type(&fields, false).into())
                }
            } else {
                // No capture info - use empty struct as fallback
                Some(context.struct_type(&[], false).into())
            }
        }
        TyKind::ExistentialSelf(_) => unreachable!("erased Self has no independent storage layout"),
        TyKind::Infer(_) | TyKind::Error => unreachable!(),
        TyKind::Opaque(_) => {
            // Opaque types have no known layout - they can only appear behind pointers
            unreachable!(
                "ICE: opaque type used directly in codegen: {}",
                ty.format(gcx)
            )
        }
    }
}

fn string_header_ty<'llvm>(context: &'llvm Context, target_data: &TargetData) -> StructType<'llvm> {
    let name = "_stringHeader";
    let ty = context
        .get_struct_type(name)
        .unwrap_or_else(|| context.opaque_struct_type(name));
    if ty.is_opaque() {
        let ptr = context.ptr_type(AddressSpace::default());
        let len = uint_from_kind(context, target_data, UIntTy::USize);
        let fields = vec![ptr.into(), len.into()];
        ty.set_body(&fields, false);
    }
    ty
}

fn int_from_kind<'llvm>(
    context: &'llvm Context,
    target_data: &TargetData,
    ty: IntTy,
) -> IntType<'llvm> {
    match ty {
        IntTy::I8 => context.i8_type(),
        IntTy::I16 => context.i16_type(),
        IntTy::I32 => context.i32_type(),
        IntTy::I64 => context.i64_type(),
        IntTy::ISize => context.ptr_sized_int_type(target_data, None),
    }
}

fn uint_from_kind<'llvm>(
    context: &'llvm Context,
    target_data: &TargetData,
    ty: UIntTy,
) -> IntType<'llvm> {
    match ty {
        UIntTy::U8 => context.i8_type(),
        UIntTy::U16 => context.i16_type(),
        UIntTy::U32 => context.i32_type(),
        UIntTy::U64 => context.i64_type(),
        UIntTy::USize => context.ptr_sized_int_type(target_data, None),
    }
}

fn is_signed(ty: Ty) -> bool {
    matches!(ty.kind(), TyKind::Int(_))
}

/// Places reached through a pointer may be shared with other threads.
fn place_is_shared(place: &mir::Place<'_>) -> bool {
    place
        .projection
        .iter()
        .any(|elem| matches!(elem, mir::PlaceElem::Deref))
}

/// Pointer leaves are split out of small aggregates; larger ones and
/// pointer-free values keep one plain access.
const MAX_SHARED_ACCESS_LEAVES: usize = 8;

fn shared_access_splits(ty: BasicTypeEnum<'_>) -> bool {
    fn leaves(ty: BasicTypeEnum<'_>) -> Option<usize> {
        match ty {
            BasicTypeEnum::StructType(struct_ty) => {
                if struct_ty.is_packed() || struct_ty.is_opaque() {
                    return None;
                }
                struct_ty
                    .get_field_types()
                    .into_iter()
                    .try_fold(0usize, |total, field| Some(total + leaves(field)?))
            }
            BasicTypeEnum::ArrayType(array_ty) => {
                leaves(array_ty.get_element_type())?.checked_mul(array_ty.len() as usize)
            }
            BasicTypeEnum::VectorType(_) => None,
            _ => Some(1),
        }
    }
    llvm_type_contains_pointer(ty)
        && leaves(ty).is_some_and(|count| count <= MAX_SHARED_ACCESS_LEAVES)
}

fn llvm_type_contains_pointer(ty: BasicTypeEnum<'_>) -> bool {
    match ty {
        BasicTypeEnum::PointerType(_) => true,
        BasicTypeEnum::StructType(struct_ty) => struct_ty
            .get_field_types()
            .into_iter()
            .any(llvm_type_contains_pointer),
        BasicTypeEnum::ArrayType(array_ty) => {
            llvm_type_contains_pointer(array_ty.get_element_type())
        }
        _ => false,
    }
}
