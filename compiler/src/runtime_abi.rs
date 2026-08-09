//! Canonical compiler/runtime ABI definition.
//!
//! Synthetic compiler declarations are generated from the typed entries in
//! this module. The same table is fingerprinted into runtime artifact
//! manifests, so changing any symbol or signature requires an explicit ABI
//! revision update.

use std::fmt::Write as _;

pub const RUNTIME_ABI_REVISION: u32 = 17;
pub const RUNTIME_MANIFEST_SCHEMA: u32 = 1;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RuntimeGcEffect {
    NoGc,
    RuntimeSafepoint,
    BlockingSafepoint,
}

/// How one argument may escape through a compiler-known runtime entry.
///
/// Runtime calls default conservatively; the explicit `NoCapture` case is
/// reserved for entries whose contract guarantees that the pointer is only
/// observed for the duration of the call.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RuntimeParamEscapeEffect {
    NoCapture,
    Capture,
    Return,
    CaptureAndReturn,
}

impl RuntimeGcEffect {
    const fn name(self) -> &'static str {
        match self {
            Self::NoGc => "nogc",
            Self::RuntimeSafepoint => "runtime-safepoint",
            Self::BlockingSafepoint => "blocking-safepoint",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RuntimeAbiType {
    Void,
    Never,
    Bool,
    U8,
    U32,
    U64,
    Usize,
    String,
    MutU8Ptr,
    ConstU8Ptr,
    AsyncHandle,
    GcDescPtr,
}

impl RuntimeAbiType {
    pub const fn name(self) -> &'static str {
        match self {
            Self::Void => "void",
            Self::Never => "never",
            Self::Bool => "bool",
            Self::U8 => "u8",
            Self::U32 => "u32",
            Self::U64 => "u64",
            Self::Usize => "usize",
            Self::String => "string",
            Self::MutU8Ptr => "*mut u8",
            Self::ConstU8Ptr => "*const u8",
            Self::AsyncHandle => "async_handle",
            Self::GcDescPtr => "*const gc_desc",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RuntimeFunctionSpec {
    pub symbol: &'static str,
    pub inputs: &'static [RuntimeAbiType],
    pub output: RuntimeAbiType,
}

impl RuntimeFunctionSpec {
    pub fn signature(self) -> String {
        let inputs = self
            .inputs
            .iter()
            .map(|ty| ty.name())
            .collect::<Vec<_>>()
            .join(",");
        format!("({inputs})->{}", self.output.name())
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RuntimeAbiFunction {
    Create,
    Poll,
    Destroy,
    CancelHandle,
    RunRoot,
    Spawn,
    FromSpawnedChecked,
    SelectTasks,
    TaskTimeout,
    Blocking,
    CleanupRegister,
    TaskCompletionStatus,
    ReclaimSpawned,
    CancelTask,
    DetachTask,
    DropTask,
    WaitReadable,
    WaitWritable,
    ChannelWaitSend,
    ChannelWaitRecv,
    MutexLock,
    RwLockRead,
    RwLockWrite,
    Sleep,
    YieldNow,
    IsTaskCancelled,
    DumpTasks,
    TaskGroupCreate,
    TaskGroupSpawn,
    TaskGroupClose,
    TaskGroupCancelAll,
    TaskGroupDestroy,
    TaskGroupDestroyAndRethrowPanic,
    TaskGroupNextStatus,
    GroupNext,
    TakeTaskPanicPayload,
    PanicPayloadMessage,
    PanicPayloadRethrow,
}

use RuntimeAbiType as T;

impl RuntimeAbiFunction {
    pub const ALL: &'static [Self] = &[
        Self::Create,
        Self::Poll,
        Self::Destroy,
        Self::CancelHandle,
        Self::RunRoot,
        Self::Spawn,
        Self::FromSpawnedChecked,
        Self::SelectTasks,
        Self::TaskTimeout,
        Self::Blocking,
        Self::CleanupRegister,
        Self::TaskCompletionStatus,
        Self::ReclaimSpawned,
        Self::CancelTask,
        Self::DetachTask,
        Self::DropTask,
        Self::WaitReadable,
        Self::WaitWritable,
        Self::ChannelWaitSend,
        Self::ChannelWaitRecv,
        Self::MutexLock,
        Self::RwLockRead,
        Self::RwLockWrite,
        Self::Sleep,
        Self::YieldNow,
        Self::IsTaskCancelled,
        Self::DumpTasks,
        Self::TaskGroupCreate,
        Self::TaskGroupSpawn,
        Self::TaskGroupClose,
        Self::TaskGroupCancelAll,
        Self::TaskGroupDestroy,
        Self::TaskGroupDestroyAndRethrowPanic,
        Self::TaskGroupNextStatus,
        Self::GroupNext,
        Self::TakeTaskPanicPayload,
        Self::PanicPayloadMessage,
        Self::PanicPayloadRethrow,
    ];

    pub const fn spec(self) -> RuntimeFunctionSpec {
        match self {
            Self::Create => spec(
                "__rt__async_create",
                &[T::MutU8Ptr, T::ConstU8Ptr, T::ConstU8Ptr, T::U8],
                T::AsyncHandle,
            ),
            Self::Poll => spec("__rt__async_poll", &[T::AsyncHandle, T::MutU8Ptr], T::U8),
            Self::Destroy => spec("__rt__async_destroy", &[T::AsyncHandle], T::Void),
            Self::CancelHandle => spec("__rt__async_cancel", &[T::AsyncHandle], T::Void),
            Self::RunRoot => spec(
                "__rt__async_run_root",
                &[T::AsyncHandle, T::MutU8Ptr],
                T::Void,
            ),
            Self::Spawn => spec(
                "__rt__executor_spawn_with_metadata",
                &[
                    T::AsyncHandle,
                    T::Usize,
                    T::String,
                    T::String,
                    T::Usize,
                    T::Usize,
                ],
                T::Usize,
            ),
            Self::FromSpawnedChecked => spec(
                "__rt__async_from_spawned_checked",
                &[T::Usize],
                T::AsyncHandle,
            ),
            Self::SelectTasks => spec(
                "__rt__async_select_tasks",
                &[T::Usize, T::Usize],
                T::AsyncHandle,
            ),
            Self::TaskTimeout => spec(
                "__rt__async_task_timeout",
                &[T::Usize, T::U64, T::U32],
                T::AsyncHandle,
            ),
            Self::Blocking => spec(
                "__rt__async_blocking",
                &[T::AsyncHandle, T::Usize, T::GcDescPtr],
                T::AsyncHandle,
            ),
            Self::CleanupRegister => spec(
                "__rt__cleanup_register",
                &[T::ConstU8Ptr, T::AsyncHandle],
                T::Usize,
            ),
            Self::TaskCompletionStatus => {
                spec("__rt__executor_task_completion_status", &[T::Usize], T::U8)
            }
            Self::ReclaimSpawned => spec("__rt__executor_reclaim_spawned", &[T::Usize], T::Void),
            Self::CancelTask => spec("__rt__executor_cancel_task", &[T::Usize], T::Void),
            Self::DetachTask => spec("__rt__executor_detach_task", &[T::Usize], T::Void),
            Self::DropTask => spec("__rt__executor_drop_task", &[T::Usize], T::Void),
            Self::WaitReadable => spec("__rt__async_wait_readable", &[T::Usize], T::AsyncHandle),
            Self::WaitWritable => spec("__rt__async_wait_writable", &[T::Usize], T::AsyncHandle),
            Self::ChannelWaitSend => spec(
                "__rt__async_channel_wait_send",
                &[T::MutU8Ptr],
                T::AsyncHandle,
            ),
            Self::ChannelWaitRecv => spec(
                "__rt__async_channel_wait_recv",
                &[T::MutU8Ptr],
                T::AsyncHandle,
            ),
            Self::MutexLock => spec("__rt__async_mutex_lock", &[T::MutU8Ptr], T::AsyncHandle),
            Self::RwLockRead => spec("__rt__async_rwlock_read", &[T::MutU8Ptr], T::AsyncHandle),
            Self::RwLockWrite => spec("__rt__async_rwlock_write", &[T::MutU8Ptr], T::AsyncHandle),
            Self::Sleep => spec("__rt__async_sleep", &[T::U64, T::U32], T::AsyncHandle),
            Self::YieldNow => spec("__rt__async_yield_now", &[], T::AsyncHandle),
            Self::IsTaskCancelled => spec("__rt__executor_is_current_task_cancelled", &[], T::Bool),
            Self::DumpTasks => spec("__rt__executor_dump_tasks", &[], T::Void),
            Self::TaskGroupCreate => spec("__rt__task_group_create", &[T::Usize, T::U8], T::Usize),
            Self::TaskGroupSpawn => spec(
                "__rt__task_group_spawn_with_metadata",
                &[
                    T::Usize,
                    T::AsyncHandle,
                    T::Usize,
                    T::String,
                    T::String,
                    T::Usize,
                    T::Usize,
                ],
                T::Usize,
            ),
            Self::TaskGroupClose => spec("__rt__task_group_close", &[T::Usize], T::Void),
            Self::TaskGroupCancelAll => spec("__rt__task_group_cancel_all", &[T::Usize], T::Void),
            Self::TaskGroupDestroy => spec("__rt__task_group_destroy", &[T::Usize], T::Void),
            Self::TaskGroupDestroyAndRethrowPanic => spec(
                "__rt__task_group_destroy_and_rethrow_panic",
                &[T::Usize],
                T::Void,
            ),
            Self::TaskGroupNextStatus => spec("__rt__task_group_next_status", &[T::Usize], T::U8),
            Self::GroupNext => spec("__rt__async_group_next", &[T::Usize], T::AsyncHandle),
            Self::TakeTaskPanicPayload => spec(
                "__rt__executor_take_task_panic_payload",
                &[T::Usize],
                T::String,
            ),
            Self::PanicPayloadMessage => {
                spec("__rt__panic_payload_message", &[T::String], T::String)
            }
            Self::PanicPayloadRethrow => {
                spec("__rt__panic_payload_rethrow", &[T::String], T::Never)
            }
        }
    }

    pub const fn gc_effect(self) -> RuntimeGcEffect {
        use RuntimeAbiFunction as F;
        match self {
            F::Poll
            | F::Destroy
            | F::CancelHandle
            | F::RunRoot
            | F::Blocking
            | F::ReclaimSpawned
            | F::DropTask
            | F::TaskGroupDestroy
            | F::TaskGroupDestroyAndRethrowPanic
            | F::TakeTaskPanicPayload
            | F::PanicPayloadRethrow => RuntimeGcEffect::RuntimeSafepoint,
            F::Create
            | F::Spawn
            | F::FromSpawnedChecked
            | F::SelectTasks
            | F::TaskTimeout
            | F::CleanupRegister
            | F::TaskCompletionStatus
            | F::CancelTask
            | F::DetachTask
            | F::WaitReadable
            | F::WaitWritable
            | F::ChannelWaitSend
            | F::ChannelWaitRecv
            | F::MutexLock
            | F::RwLockRead
            | F::RwLockWrite
            | F::Sleep
            | F::YieldNow
            | F::IsTaskCancelled
            | F::DumpTasks
            | F::TaskGroupCreate
            | F::TaskGroupSpawn
            | F::TaskGroupClose
            | F::TaskGroupCancelAll
            | F::TaskGroupNextStatus
            | F::GroupNext
            | F::PanicPayloadMessage => RuntimeGcEffect::NoGc,
        }
    }

    /// Escape behavior for a concrete parameter of this runtime entry.
    ///
    /// Keeping this as an exhaustive match means adding a runtime function is
    /// also a compile-time request to classify its arguments.
    pub const fn param_escape_effect(self, parameter: usize) -> Option<RuntimeParamEscapeEffect> {
        if parameter >= self.spec().inputs.len() {
            return None;
        }

        use RuntimeAbiFunction as F;
        use RuntimeParamEscapeEffect as E;
        Some(match self {
            // The created handle owns the frame. Polling and terminal handle
            // operations only observe their arguments for the call duration.
            F::Create => {
                if parameter == 0 {
                    E::CaptureAndReturn
                } else {
                    E::Capture
                }
            }
            F::Poll | F::Destroy | F::CancelHandle | F::RunRoot => E::NoCapture,

            // Executor registration retains the handle and diagnostic strings.
            F::Spawn | F::CleanupRegister | F::TaskGroupSpawn => E::Capture,
            F::Blocking => {
                if parameter == 0 {
                    E::CaptureAndReturn
                } else {
                    E::NoCapture
                }
            }

            // These entries consume scalar handles/identifiers or synchronously
            // inspect output storage without retaining its address.
            F::FromSpawnedChecked
            | F::SelectTasks
            | F::TaskTimeout
            | F::TaskCompletionStatus
            | F::ReclaimSpawned
            | F::CancelTask
            | F::DetachTask
            | F::DropTask
            | F::WaitReadable
            | F::WaitWritable
            | F::Sleep
            | F::IsTaskCancelled
            | F::TaskGroupCreate
            | F::TaskGroupClose
            | F::TaskGroupCancelAll
            | F::TaskGroupDestroy
            | F::TaskGroupDestroyAndRethrowPanic
            | F::TaskGroupNextStatus
            | F::GroupNext
            | F::TakeTaskPanicPayload => E::NoCapture,

            // The returned awaitable retains the synchronization object.
            F::ChannelWaitSend
            | F::ChannelWaitRecv
            | F::MutexLock
            | F::RwLockRead
            | F::RwLockWrite => E::CaptureAndReturn,

            F::PanicPayloadMessage => E::Return,
            F::PanicPayloadRethrow => E::Capture,

            // No parameters; the bounds check above makes these unreachable.
            F::YieldNow | F::DumpTasks => E::NoCapture,
        })
    }
}

const fn spec(
    symbol: &'static str,
    inputs: &'static [RuntimeAbiType],
    output: RuntimeAbiType,
) -> RuntimeFunctionSpec {
    RuntimeFunctionSpec {
        symbol,
        inputs,
        output,
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct AdditionalRuntimeSymbol {
    pub symbol: &'static str,
    pub signature: &'static str,
    pub availability: RuntimeSymbolAvailability,
    pub gc_effect: RuntimeGcEffect,
    pub param_escape_effect: RuntimeParamEscapeEffect,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RuntimeSymbolAvailability {
    AllTargets,
    Unix,
}

impl RuntimeSymbolAvailability {
    const fn name(self) -> &'static str {
        match self {
            Self::AllTargets => "all",
            Self::Unix => "unix",
        }
    }

    fn supports(self, target: &str) -> bool {
        match self {
            Self::AllTargets => true,
            Self::Unix => {
                target == "host-unix"
                    || target.contains("linux")
                    || target.contains("darwin")
                    || target.contains("apple")
                    || target.contains("freebsd")
                    || target.contains("netbsd")
                    || target.contains("openbsd")
                    || target.contains("dragonfly")
                    || target.contains("solaris")
                    || target.contains("illumos")
                    || target.contains("android")
            }
        }
    }
}

/// ABI entries referenced directly by codegen or declared by the standard
/// library rather than synthesized through `RuntimeAbiFunction`.
pub const ADDITIONAL_RUNTIME_SYMBOLS: &[AdditionalRuntimeSymbol] = &[
    additional("__rt__bench_next_batch", "()->usize"),
    additional_safepoint(
        "__rt__bench_run_case",
        "(fn()->void,*const u8,usize,*const u8,usize,bool,*const u8,usize)->u8",
    ),
    additional("__rt__bench_set_bytes", "(usize)->void"),
    additional("__rt__black_box", "(*mut u8,usize)->void"),
    additional("__rt__install_stack_guard", "()->void"),
    additional_safepoint("__gc__alloc", "(usize,*const gc_desc)->*mut u8"),
    additional_safepoint("__gc__collect", "()->void"),
    additional_safepoint(
        "__gc__grow_buf",
        "(*mut u8,*const gc_desc,usize,usize)->*mut u8",
    ),
    additional_safepoint("__gc__makebuf", "(*const gc_desc,usize,usize)->*mut u8"),
    additional_safepoint("__gc__poll", "()->void"),
    additional("__gc__poll_flags", "atomic u8"),
    additional("__gc__register_static", "(*const u8,*const gc_desc)->void"),
    additional("__gc__set_buf_len", "(*mut u8,*const gc_desc,usize)->void"),
    additional_safepoint("__gc__thread_enter_managed", "()->void"),
    additional("__rt__cleanup_cancel", "(usize)->bool"),
    additional_blocking("__rt__cleanup_wait", "()->void"),
    additional("__rt__async_io_adopt_fd", "(i32)->usize"),
    additional("__rt__async_io_close_source", "(usize)->i32"),
    additional("__rt__async_io_dup", "(i32)->i32"),
    additional("__rt__async_io_pipe", "(*mut i32,*mut i32)->i32"),
    additional("__rt__async_io_read_source", "(usize,*mut u8,usize)->isize"),
    additional(
        "__rt__async_io_write_source",
        "(usize,*const u8,usize)->isize",
    ),
    additional_safepoint("__rt__executor_abort_rootless", "()->void"),
    additional_safepoint("__rt__executor_finish_rootless", "()->void"),
    additional_unix_blocking("__rt__env_current_dir", "(*mut *mut u8,*mut usize)->i32"),
    additional_unix_blocking(
        "__rt__env_get",
        "(string,*mut *mut u8,*mut usize,*mut bool)->i32",
    ),
    additional_unix_blocking("__rt__env_home_dir", "(*mut *mut u8,*mut usize)->i32"),
    additional_unix("__rt__env_owned_bytes_free", "(*mut u8)->void"),
    additional_unix_blocking("__rt__env_remove", "(string)->i32"),
    additional_unix_blocking("__rt__env_set", "(string,string)->i32"),
    additional_unix_blocking("__rt__env_set_current_dir", "(string)->i32"),
    additional_unix(
        "__rt__env_snapshot_at",
        "(usize,usize,*mut *const u8,*mut usize,*mut *const u8,*mut usize)->i32",
    ),
    additional_unix("__rt__env_snapshot_close", "(usize)->void"),
    additional_unix_blocking("__rt__env_snapshot_open", "(*mut usize)->usize"),
    additional_unix_blocking("__rt__env_temp_dir", "(*mut *mut u8,*mut usize)->i32"),
    additional_unix_blocking(
        "__rt__fs_canonicalize",
        "(string,*mut *mut u8,*mut usize)->i32",
    ),
    additional_unix_blocking("__rt__fs_copy", "(string,string,*mut u64)->i32"),
    additional_unix_blocking(
        "__rt__fs_create_temp_dir",
        "(string,string,*mut *mut u8,*mut usize)->i32",
    ),
    additional_unix_blocking("__rt__fs_dir_close", "(usize)->i32"),
    additional_unix_blocking("__rt__fs_dir_open", "(string,*mut i32)->usize"),
    additional_unix_blocking(
        "__rt__fs_dir_read",
        "(usize,*mut *mut u8,*mut usize,*mut u8)->i32",
    ),
    additional_unix_blocking(
        "__rt__fs_metadata",
        "(string,bool,*mut u8,*mut u64,*mut i64,*mut u32,*mut i64,*mut u32)->i32",
    ),
    additional_unix("__rt__fs_owned_bytes_free", "(*mut u8)->void"),
    additional_unix_blocking("__rt__fs_remove_dir_all", "(string)->i32"),
    additional(
        "__rt__existential_lookup_conformance",
        "(*const u8,*const u8)->*const u8",
    ),
    additional("__rt__gc_enter_blocking", "()->void"),
    additional("__rt__gc_exit_blocking", "()->void"),
    additional(
        "__rt__pc_metadata_register",
        "(*const pc_metadata_module)->void",
    ),
    additional("__rt__hash_seed0", "()->u64"),
    additional("__rt__hash_seed1", "()->u64"),
    additional_with_escape(
        "__rt__keep_alive",
        "(*const u8)->void",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix(
        "__rt__net_ip_snapshot_at",
        "(usize,usize,*mut u8,*mut u8)->i32",
    ),
    additional_unix_blocking(
        "__rt__net_lookup_address",
        "(u8,*const u8,*mut usize,*mut u8,*mut i32,*mut i32)->usize",
    ),
    additional_unix_blocking(
        "__rt__net_lookup_host",
        "(string,*mut usize,*mut u8,*mut i32,*mut i32)->usize",
    ),
    additional_unix(
        "__rt__net_name_snapshot_at",
        "(usize,usize,*mut *const u8,*mut usize)->i32",
    ),
    additional_unix("__rt__net_snapshot_close", "(usize)->void"),
    additional_unix_blocking("__rt__open2", "(*const u8,i32)->i32"),
    additional_unix_blocking("__rt__open3", "(*const u8,i32,i32)->i32"),
    additional("__rt__parse_f32", "(string,*mut u32)->u8"),
    additional("__rt__parse_f64", "(string,*mut u64)->u8"),
    additional_safepoint("__rt__panic_abort", "(string)->never"),
    additional_safepoint("__rt__panic_abort_unwind", "(*mut u8)->never"),
    additional_safepoint("__rt__panic_unwind", "(string)->never"),
    additional_safepoint(
        "__rt__panic_unwind_at",
        "(string,string,usize,usize)->never",
    ),
    additional_unix("__rt__process_child_abandon", "(usize)->void"),
    additional_unix("__rt__process_child_kill", "(usize)->i32"),
    additional_unix("__rt__process_child_pid", "(usize,*mut u32)->i32"),
    additional_unix(
        "__rt__process_child_try_wait",
        "(usize,*mut bool,*mut i32,*mut i32)->i32",
    ),
    additional_unix_blocking("__rt__process_child_wait", "(usize,*mut i32,*mut i32)->i32"),
    additional_unix("__rt__process_command_arg", "(usize,string)->i32"),
    additional_unix("__rt__process_command_close", "(usize)->void"),
    additional_unix("__rt__process_command_current_dir", "(usize,string)->i32"),
    additional_unix("__rt__process_command_env", "(usize,string,string)->i32"),
    additional_unix("__rt__process_command_open", "(string,*mut i32)->usize"),
    additional_unix_blocking(
        "__rt__process_command_output",
        "(usize,bool,usize,*mut i32,*mut bool)->usize",
    ),
    additional_unix_blocking(
        "__rt__process_command_spawn",
        "(usize,*mut usize,*mut i32,*mut i32,*mut i32)->i32",
    ),
    additional_unix_blocking(
        "__rt__process_command_status",
        "(usize,*mut i32,*mut i32)->i32",
    ),
    additional_unix("__rt__process_command_stdio", "(usize,u8,u8,u8)->i32"),
    additional_unix("__rt__process_output_close", "(usize)->void"),
    additional_unix(
        "__rt__process_output_stderr",
        "(usize,*mut *const u8,*mut usize)->i32",
    ),
    additional_unix(
        "__rt__process_output_status",
        "(usize,*mut i32,*mut i32)->i32",
    ),
    additional_unix(
        "__rt__process_output_stdout",
        "(usize,*mut *const u8,*mut usize)->i32",
    ),
    additional("__rt__sync_channel_close", "(*mut u8)->i32"),
    additional_safepoint(
        "__rt__sync_channel_create",
        "(usize,usize,u8,*const gc_desc)->*mut u8",
    ),
    additional("__rt__sync_channel_destroy", "(*mut u8)->i32"),
    additional("__rt__sync_channel_try_recv", "(*mut u8,*mut u8)->i32"),
    additional("__rt__sync_channel_try_send", "(*mut u8,*const u8)->i32"),
    additional_safepoint("__rt__sync_mutex_create", "()->*mut u8"),
    additional("__rt__sync_mutex_destroy", "(*mut u8)->i32"),
    additional("__rt__sync_mutex_try_lock", "(*mut u8)->i32"),
    additional("__rt__sync_mutex_unlock", "(*mut u8)->i32"),
    additional_safepoint("__rt__sync_rwlock_create", "()->*mut u8"),
    additional("__rt__sync_rwlock_destroy", "(*mut u8)->i32"),
    additional("__rt__sync_rwlock_try_read", "(*mut u8)->i32"),
    additional("__rt__sync_rwlock_try_write", "(*mut u8)->i32"),
    additional("__rt__sync_rwlock_unlock_read", "(*mut u8)->i32"),
    additional("__rt__sync_rwlock_unlock_write", "(*mut u8)->i32"),
    additional_safepoint("__rt__test_call_fn", "(fn()->void)->bool"),
    additional_safepoint("__rt__test_gc_collect_probe_is_live", "(*mut u8)->bool"),
    additional_safepoint("__rt__test_gc_probe_create", "(*const u8)->*mut u8"),
    additional("__rt__test_panic_finish", "(bool,*const u8,usize)->void"),
    additional("__rt__test_panic_status", "(bool,*const u8,usize)->u8"),
    additional_safepoint("__rt__weak_create", "(*const u8)->*mut u8"),
    additional_safepoint("__rt__weak_value", "(*mut u8)->*mut u8"),
];

const fn additional(symbol: &'static str, signature: &'static str) -> AdditionalRuntimeSymbol {
    additional_with_escape(
        symbol,
        signature,
        RuntimeParamEscapeEffect::CaptureAndReturn,
    )
}

const fn additional_with_escape(
    symbol: &'static str,
    signature: &'static str,
    param_escape_effect: RuntimeParamEscapeEffect,
) -> AdditionalRuntimeSymbol {
    AdditionalRuntimeSymbol {
        symbol,
        signature,
        availability: RuntimeSymbolAvailability::AllTargets,
        gc_effect: RuntimeGcEffect::NoGc,
        param_escape_effect,
    }
}

const fn additional_safepoint(
    symbol: &'static str,
    signature: &'static str,
) -> AdditionalRuntimeSymbol {
    AdditionalRuntimeSymbol {
        symbol,
        signature,
        availability: RuntimeSymbolAvailability::AllTargets,
        gc_effect: RuntimeGcEffect::RuntimeSafepoint,
        param_escape_effect: RuntimeParamEscapeEffect::CaptureAndReturn,
    }
}

const fn additional_blocking(
    symbol: &'static str,
    signature: &'static str,
) -> AdditionalRuntimeSymbol {
    AdditionalRuntimeSymbol {
        symbol,
        signature,
        availability: RuntimeSymbolAvailability::AllTargets,
        gc_effect: RuntimeGcEffect::BlockingSafepoint,
        param_escape_effect: RuntimeParamEscapeEffect::CaptureAndReturn,
    }
}

const fn additional_unix(symbol: &'static str, signature: &'static str) -> AdditionalRuntimeSymbol {
    AdditionalRuntimeSymbol {
        symbol,
        signature,
        availability: RuntimeSymbolAvailability::Unix,
        gc_effect: RuntimeGcEffect::NoGc,
        param_escape_effect: RuntimeParamEscapeEffect::CaptureAndReturn,
    }
}

const fn additional_unix_blocking(
    symbol: &'static str,
    signature: &'static str,
) -> AdditionalRuntimeSymbol {
    AdditionalRuntimeSymbol {
        symbol,
        signature,
        availability: RuntimeSymbolAvailability::Unix,
        gc_effect: RuntimeGcEffect::BlockingSafepoint,
        param_escape_effect: RuntimeParamEscapeEffect::CaptureAndReturn,
    }
}

pub fn required_symbols() -> impl Iterator<Item = &'static str> {
    RuntimeAbiFunction::ALL
        .iter()
        .map(|function| function.spec().symbol)
        .chain(ADDITIONAL_RUNTIME_SYMBOLS.iter().map(|entry| entry.symbol))
}

pub fn required_symbols_for_target(target: &str) -> impl Iterator<Item = &'static str> + '_ {
    RuntimeAbiFunction::ALL
        .iter()
        .map(|function| function.spec().symbol)
        .chain(
            ADDITIONAL_RUNTIME_SYMBOLS
                .iter()
                .filter(|entry| entry.availability.supports(target))
                .map(|entry| entry.symbol),
        )
}

pub fn gc_effect_for_symbol(symbol: &str) -> Option<RuntimeGcEffect> {
    RuntimeAbiFunction::ALL
        .iter()
        .find_map(|function| (function.spec().symbol == symbol).then(|| function.gc_effect()))
        .or_else(|| {
            ADDITIONAL_RUNTIME_SYMBOLS
                .iter()
                .find_map(|entry| (entry.symbol == symbol).then_some(entry.gc_effect))
        })
}

/// Return the escape contract for a parameter of a canonical runtime symbol.
///
/// Most runtime APIs are intentionally conservative in this first instance-
/// aware analysis. Keeping the classification in the canonical ABI module
/// prevents name-based exceptions from accumulating in MIR passes.
pub fn param_escape_effect_for_symbol(
    symbol: &str,
    parameter: usize,
) -> Option<RuntimeParamEscapeEffect> {
    RuntimeAbiFunction::ALL
        .iter()
        .find(|function| function.spec().symbol == symbol)
        .and_then(|function| function.param_escape_effect(parameter))
        .or_else(|| {
            ADDITIONAL_RUNTIME_SYMBOLS
                .iter()
                .find(|entry| entry.symbol == symbol)
                .map(|entry| entry.param_escape_effect)
        })
}

/// Escape contract for compiler-lowered intrinsics.
///
/// Unlike arbitrary foreign calls, intrinsics execute as part of the current
/// operation and cannot retain arguments unless their documented lowering
/// explicitly publishes a value. `None` deliberately rejects unknown entries
/// so adding an intrinsic also requires reviewing its escape behavior.
pub fn intrinsic_param_escape_effect(
    symbol: &str,
    parameter: usize,
) -> Option<RuntimeParamEscapeEffect> {
    use RuntimeParamEscapeEffect as E;

    let effect = match symbol {
        // Identity or pointer-producing operations return provenance from the
        // first argument without retaining it.
        "__intrinsic_black_box"
        | "__intrinsic_array_read_unchecked"
        | "__intrinsic_array_read_mut_unchecked"
        | "__intrinsic_list_read_unchecked"
        | "__intrinsic_list_read_mut_unchecked"
        | "__intrinsic_ref_to_ptr"
        | "__intrinsic_mut_ref_to_ptr"
        | "__intrinsic_ptr_to_u8"
        | "__intrinsic_ptr_to_u8_mut"
        | "__intrinsic_ptr_add"
        | "__intrinsic_ptr_sub"
        | "__intrinsic_ptr_offset"
        | "__intrinsic_ptr_byte_add"
        | "__intrinsic_ptr_byte_sub"
        | "__intrinsic_ptr_read"
        | "__intrinsic_string_from_parts"
        | "__intrinsic_string_data"
            if parameter == 0 =>
        {
            E::Return
        }

        // These operations publish argument bytes into storage that may be
        // managed or otherwise outlive the call. The destination pointer is
        // only observed for the duration of the intrinsic.
        "__intrinsic_array_write_unchecked" | "__intrinsic_list_write" if parameter == 2 => {
            E::Capture
        }
        "__intrinsic_ptr_write" if parameter == 1 => E::Capture,
        "__intrinsic_memcpy" | "__intrinsic_memmove" if parameter == 1 => E::Capture,

        // Async constructors retain closures/state in their returned future
        // or task. Source-async placement is additionally conservative before
        // coroutine lowering.
        "__intrinsic_spawn_async" | "__intrinsic_blocking" if parameter == 0 => E::CaptureAndReturn,
        "__intrinsic_add_cleanup" => E::Capture,
        "__intrinsic_select_tasks"
        | "__intrinsic_task_timeout"
        | "__intrinsic_task_result"
        | "__intrinsic_channel_wait_send"
        | "__intrinsic_channel_wait_recv"
        | "__intrinsic_mutex_lock"
        | "__intrinsic_rwlock_read"
        | "__intrinsic_rwlock_write" => E::CaptureAndReturn,
        "__intrinsic_task_group_spawn" if parameter == 1 => E::Capture,

        // Synchronous value/scalar operations and handle-only runtime shims do
        // not retain or return argument provenance.
        "__intrinsic_black_box"
        | "__intrinsic_array_read_unchecked"
        | "__intrinsic_array_read_mut_unchecked"
        | "__intrinsic_list_read_unchecked"
        | "__intrinsic_list_read_mut_unchecked"
        | "__intrinsic_ref_to_ptr"
        | "__intrinsic_mut_ref_to_ptr"
        | "__intrinsic_ptr_to_u8"
        | "__intrinsic_ptr_to_u8_mut"
        | "__intrinsic_ptr_add"
        | "__intrinsic_ptr_sub"
        | "__intrinsic_ptr_offset"
        | "__intrinsic_ptr_byte_add"
        | "__intrinsic_ptr_byte_sub"
        | "__intrinsic_ptr_read"
        | "__intrinsic_string_from_parts"
        | "__intrinsic_string_data"
        | "__intrinsic_spawn_async"
        | "__intrinsic_blocking"
        | "__intrinsic_task_group_spawn"
        | "__intrinsic_array_write_unchecked"
        | "__intrinsic_list_write"
        | "__intrinsic_ptr_write"
        | "__intrinsic_memcpy"
        | "__intrinsic_memmove"
        | "__intrinsic_memset"
        | "__intrinsic_string_len"
        | "__intrinsic_size_of"
        | "__intrinsic_align_of"
        | "__intrinsic_maybe_uninit"
        | "__intrinsic_gc_desc"
        | "__intrinsic_env_argc"
        | "__intrinsic_env_argv"
        | "__intrinsic_rune_from_u32_unchecked"
        | "__intrinsic_cancel_task"
        | "__intrinsic_detach_task"
        | "__intrinsic_dump_tasks"
        | "__intrinsic_is_task_cancelled"
        | "__intrinsic_task_group_create"
        | "__intrinsic_task_group_close"
        | "__intrinsic_task_group_cancel"
        | "__intrinsic_task_group_destroy"
        | "__intrinsic_task_group_destroy_and_rethrow"
        | "__intrinsic_task_group_next"
        | "__intrinsic_wait_readable"
        | "__intrinsic_wait_writable"
        | "__intrinsic_sleep"
        | "__intrinsic_panic_payload_message"
        | "__intrinsic_panic_payload_rethrow" => E::NoCapture,

        // Checked arithmetic and typed math names are a closed compiler-owned
        // family. They operate only on scalar operands.
        name if name.starts_with("__intrinsic_checked_") || is_typed_math_intrinsic_name(name) => {
            E::NoCapture
        }
        _ => return None,
    };
    Some(effect)
}

/// Dereference depth for an intrinsic's `Return` effect.
pub fn intrinsic_return_deref(symbol: &str, parameter: usize) -> Option<u8> {
    (symbol == "__intrinsic_ptr_read" && parameter == 0)
        .then_some(1)
        .or(Some(0))
}

fn is_typed_math_intrinsic_name(symbol: &str) -> bool {
    const OPERATIONS: &[&str] = &[
        "sqrt",
        "sin",
        "cos",
        "tan",
        "asin",
        "acos",
        "atan",
        "sinh",
        "cosh",
        "tanh",
        "exp",
        "exp2",
        "log",
        "log2",
        "log10",
        "fabs",
        "floor",
        "ceil",
        "trunc",
        "rint",
        "nearbyint",
        "round",
        "roundeven",
        "pow",
        "powi",
        "copysign",
        "fma",
        "minimum",
        "maximum",
        "minimumnum",
        "maximumnum",
    ];
    OPERATIONS.iter().any(|operation| {
        symbol == format!("__intrinsic_{operation}")
            || symbol.starts_with(&format!("__intrinsic_{operation}_"))
    })
}

pub fn fingerprint() -> String {
    let mut canonical = format!("runtime-abi-revision={RUNTIME_ABI_REVISION}\n");
    for function in RuntimeAbiFunction::ALL {
        let spec = function.spec();
        let _ = writeln!(
            canonical,
            "{} [{}] {}",
            spec.symbol,
            function.gc_effect().name(),
            spec.signature()
        );
    }
    for entry in ADDITIONAL_RUNTIME_SYMBOLS {
        let _ = writeln!(
            canonical,
            "{} [{}] [{}] {}",
            entry.symbol,
            entry.availability.name(),
            entry.gc_effect.name(),
            entry.signature
        );
    }
    blake3::hash(canonical.as_bytes()).to_hex().to_string()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    #[test]
    fn canonical_runtime_symbols_are_unique() {
        let symbols = required_symbols().collect::<Vec<_>>();
        let unique = symbols.iter().copied().collect::<HashSet<_>>();
        assert_eq!(symbols.len(), unique.len());
    }

    #[test]
    fn every_runtime_symbol_has_an_explicit_gc_effect() {
        for symbol in required_symbols() {
            assert!(
                gc_effect_for_symbol(symbol).is_some(),
                "missing GC effect for {symbol}"
            );
        }
        assert_eq!(
            gc_effect_for_symbol("__gc__alloc"),
            Some(RuntimeGcEffect::RuntimeSafepoint)
        );
        assert_eq!(
            gc_effect_for_symbol("__rt__hash_seed0"),
            Some(RuntimeGcEffect::NoGc)
        );
        assert_eq!(
            gc_effect_for_symbol("__rt__test_gc_probe_create"),
            Some(RuntimeGcEffect::RuntimeSafepoint)
        );
        assert_eq!(
            gc_effect_for_symbol("__rt__test_gc_collect_probe_is_live"),
            Some(RuntimeGcEffect::RuntimeSafepoint)
        );
        assert_eq!(
            gc_effect_for_symbol("__rt__open2"),
            Some(RuntimeGcEffect::BlockingSafepoint)
        );
        assert_eq!(gc_effect_for_symbol("__rt__missing"), None);
    }

    #[test]
    fn every_runtime_symbol_has_an_escape_effect() {
        for function in RuntimeAbiFunction::ALL {
            let spec = function.spec();
            for parameter in 0..spec.inputs.len() {
                assert!(
                    param_escape_effect_for_symbol(spec.symbol, parameter).is_some(),
                    "missing parameter {parameter} escape effect for {}",
                    spec.symbol
                );
            }
            assert_eq!(
                function.param_escape_effect(spec.inputs.len()),
                None,
                "typed runtime entries must reject out-of-range parameters"
            );
        }
        for entry in ADDITIONAL_RUNTIME_SYMBOLS {
            assert_eq!(
                param_escape_effect_for_symbol(entry.symbol, 0),
                Some(entry.param_escape_effect),
                "additional runtime symbol must carry its classification"
            );
        }
        assert_eq!(
            param_escape_effect_for_symbol("__rt__keep_alive", 0),
            Some(RuntimeParamEscapeEffect::NoCapture)
        );
        assert_eq!(param_escape_effect_for_symbol("__rt__missing", 0), None);
    }

    #[test]
    fn fingerprint_changes_with_revision_or_signature_text() {
        assert_eq!(fingerprint().len(), 64);
        assert_ne!(fingerprint(), blake3::hash(b"").to_hex().to_string());
    }

    #[test]
    fn target_symbol_filter_preserves_unix_only_exports() {
        let unix = required_symbols_for_target("aarch64-apple-darwin").collect::<HashSet<_>>();
        let windows = required_symbols_for_target("x86_64-pc-windows-msvc").collect::<HashSet<_>>();
        assert!(unix.contains("__rt__open2"));
        assert!(unix.contains("__rt__env_get"));
        assert!(unix.contains("__rt__env_snapshot_open"));
        assert!(unix.contains("__rt__fs_metadata"));
        assert!(unix.contains("__rt__fs_remove_dir_all"));
        assert!(unix.contains("__rt__net_lookup_host"));
        assert!(unix.contains("__rt__net_lookup_address"));
        assert!(unix.contains("__rt__process_command_spawn"));
        assert!(unix.contains("__rt__process_child_wait"));
        assert!(!windows.contains("__rt__open2"));
        assert!(!windows.contains("__rt__env_get"));
        assert!(!windows.contains("__rt__env_snapshot_open"));
        assert!(!windows.contains("__rt__fs_metadata"));
        assert!(!windows.contains("__rt__fs_remove_dir_all"));
        assert!(!windows.contains("__rt__net_lookup_host"));
        assert!(!windows.contains("__rt__net_lookup_address"));
        assert!(!windows.contains("__rt__process_command_spawn"));
        assert!(!windows.contains("__rt__process_child_wait"));
    }

    #[test]
    fn scalar_parse_exports_are_part_of_the_canonical_abi() {
        let symbols = required_symbols().collect::<HashSet<_>>();
        assert!(symbols.contains("__rt__parse_f32"));
        assert!(symbols.contains("__rt__parse_f64"));
    }

    #[test]
    fn stack_guard_export_is_required_on_every_target() {
        for target in [
            "aarch64-apple-darwin",
            "x86_64-unknown-linux-gnu",
            "x86_64-pc-windows-msvc",
        ] {
            assert!(
                required_symbols_for_target(target)
                    .any(|symbol| symbol == "__rt__install_stack_guard"),
                "stack guard missing for {target}"
            );
        }
    }
}
