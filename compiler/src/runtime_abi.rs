//! Canonical compiler/runtime ABI definition.
//!
//! Synthetic compiler declarations are generated from the typed entries in
//! this module. The same table is fingerprinted into runtime artifact
//! manifests, so changing any symbol or signature requires an explicit ABI
//! revision update.

use std::fmt::Write as _;

pub const RUNTIME_ABI_REVISION: u32 = 82;
pub const RUNTIME_MANIFEST_SCHEMA: u32 = 1;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RuntimeCallEffect {
    Direct,
    Callback,
    Blocking,
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

impl RuntimeCallEffect {
    const fn name(self) -> &'static str {
        match self {
            Self::Direct => "direct",
            Self::Callback => "callback",
            Self::Blocking => "blocking",
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

    FrameData,
    CreateOwned,
    Poll,
    PollPublished,
    Destroy,
    CancelHandle,
    CancelPoll,
    CancelFrame,
    RunRoot,
    RunMain,
    Spawn,
    FromSpawnedChecked,
    SelectTasks,
    TaskTimeout,
    Blocking,
    TaskCompletionStatus,
    CancelTask,

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
        Self::FrameData,
        Self::CreateOwned,
        Self::Poll,
        Self::PollPublished,
        Self::Destroy,
        Self::CancelHandle,
        Self::CancelPoll,
        Self::CancelFrame,
        Self::RunRoot,
        Self::RunMain,
        Self::Spawn,
        Self::FromSpawnedChecked,
        Self::SelectTasks,
        Self::TaskTimeout,
        Self::Blocking,
        Self::TaskCompletionStatus,
        Self::CancelTask,
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

            Self::FrameData => spec("__rt__async_frame_data", &[T::MutU8Ptr], T::MutU8Ptr),
            Self::CreateOwned => spec(
                "__rt__async_create_owned",
                &[T::MutU8Ptr, T::ConstU8Ptr, T::ConstU8Ptr, T::U8],
                T::AsyncHandle,
            ),
            Self::Poll => spec("__rt__async_poll", &[T::AsyncHandle, T::MutU8Ptr], T::U8),
            Self::PollPublished => spec(
                "__rt__async_poll_published",
                &[T::AsyncHandle, T::MutU8Ptr, T::MutU8Ptr],
                T::U8,
            ),
            Self::Destroy => spec("__rt__async_destroy", &[T::AsyncHandle], T::Void),
            Self::CancelHandle => spec("__rt__async_cancel", &[T::AsyncHandle], T::Void),
            Self::CancelPoll => spec("__rt__async_cancel_poll", &[T::AsyncHandle], T::U8),
            Self::CancelFrame => spec(
                "__rt__async_cancel_frame",
                &[T::MutU8Ptr, T::ConstU8Ptr],
                T::Void,
            ),
            Self::RunRoot => spec(
                "__rt__async_run_root",
                &[T::AsyncHandle, T::MutU8Ptr],
                T::Void,
            ),
            Self::RunMain => spec(
                "__rt__async_run_main",
                &[T::AsyncHandle, T::MutU8Ptr],
                T::Void,
            ),
            Self::Spawn => spec(
                "__rt__task_spawn_with_metadata",
                &[
                    T::AsyncHandle,
                    T::ConstU8Ptr,
                    T::String,
                    T::String,
                    T::Usize,
                    T::Usize,
                ],
                T::MutU8Ptr,
            ),
            Self::FromSpawnedChecked => {
                spec("__rt__async_task_result", &[T::MutU8Ptr], T::AsyncHandle)
            }
            Self::SelectTasks => spec(
                "__rt__async_select_tasks",
                &[T::MutU8Ptr, T::MutU8Ptr],
                T::AsyncHandle,
            ),
            Self::TaskTimeout => spec(
                "__rt__async_task_timeout",
                &[T::MutU8Ptr, T::U64, T::U32],
                T::AsyncHandle,
            ),
            Self::Blocking => spec(
                "__rt__async_blocking",
                &[T::AsyncHandle, T::ConstU8Ptr],
                T::AsyncHandle,
            ),
            Self::TaskCompletionStatus => spec("__rt__task_status", &[T::MutU8Ptr], T::U8),
            Self::CancelTask => spec("__rt__task_cancel", &[T::MutU8Ptr], T::Void),
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
                    T::ConstU8Ptr,
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
            Self::TakeTaskPanicPayload => {
                spec("__gc__task_panic_payload", &[T::MutU8Ptr], T::String)
            }
            Self::PanicPayloadMessage => {
                spec("__rt__panic_payload_message", &[T::String], T::String)
            }
            Self::PanicPayloadRethrow => {
                spec("__rt__panic_payload_rethrow", &[T::String], T::Never)
            }
        }
    }

    pub const fn call_effect(self) -> RuntimeCallEffect {
        use RuntimeAbiFunction as F;
        match self {
            F::Poll
            | F::PollPublished
            | F::Destroy
            | F::CancelHandle
            | F::CancelPoll
            | F::CancelFrame
            | F::RunRoot
            | F::RunMain
            | F::Blocking
            | F::TaskGroupDestroy
            | F::TaskGroupDestroyAndRethrowPanic
            | F::TakeTaskPanicPayload
            | F::PanicPayloadRethrow
            | F::Spawn
            | F::TaskGroupCreate
            | F::TaskGroupSpawn => RuntimeCallEffect::Callback,
            F::Create
            | F::FrameData
            | F::CreateOwned
            | F::FromSpawnedChecked
            | F::SelectTasks
            | F::TaskTimeout
            | F::TaskCompletionStatus
            | F::CancelTask
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
            | F::TaskGroupClose
            | F::TaskGroupCancelAll
            | F::TaskGroupNextStatus
            | F::GroupNext
            | F::PanicPayloadMessage => RuntimeCallEffect::Direct,
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
            F::Create | F::CreateOwned => {
                if parameter == 0 {
                    E::CaptureAndReturn
                } else {
                    E::Capture
                }
            }

            F::FrameData => E::Return,
            F::Poll
            | F::PollPublished
            | F::Destroy
            | F::CancelHandle
            | F::CancelPoll
            | F::CancelFrame
            | F::RunRoot
            | F::RunMain => E::NoCapture,

            // Executor registration retains the handle and diagnostic strings.
            F::Spawn if parameter == 1 => E::NoCapture,
            F::TaskGroupSpawn if parameter == 2 => E::NoCapture,
            F::Spawn | F::TaskGroupSpawn => E::Capture,
            F::Blocking => {
                if parameter == 0 {
                    E::CaptureAndReturn
                } else {
                    E::NoCapture
                }
            }

            // These entries consume scalar handles/identifiers or synchronously
            // inspect output storage without retaining its address.
            // The result wait keeps the handle object rooted until it is destroyed.
            F::FromSpawnedChecked => E::CaptureAndReturn,
            F::SelectTasks
            | F::TaskTimeout
            | F::TaskCompletionStatus
            | F::CancelTask
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
    pub call_effect: RuntimeCallEffect,
    parameter_count: usize,
    param_escape_effects: AdditionalRuntimeParamEscapeEffects,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum AdditionalRuntimeParamEscapeEffects {
    Uniform(RuntimeParamEscapeEffect),
    PerParameter(&'static [RuntimeParamEscapeEffect]),
}

impl AdditionalRuntimeSymbol {
    fn param_escape_effect(&self, parameter: usize) -> Option<RuntimeParamEscapeEffect> {
        if parameter >= self.parameter_count {
            return None;
        }
        match self.param_escape_effects {
            AdditionalRuntimeParamEscapeEffects::Uniform(effect) => Some(effect),
            AdditionalRuntimeParamEscapeEffects::PerParameter(effects) => {
                effects.get(parameter).copied()
            }
        }
    }
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
    additional_callback(
        "__rt__bench_run_case",
        "(fn()->void,*const u8,usize,*const u8,usize,bool,*const u8,usize)->u8",
    ),
    additional("__rt__bench_set_bytes", "(usize)->void"),
    additional("__rt__black_box", "(*mut u8,usize)->void"),
    additional("__rt__install_stack_guard", "()->void"),
    additional_unix("__rt__fcntl_int", "(i32,i32,i32)->i32"),
    additional("__rt__async_io_adopt_fd", "(i32)->usize"),
    additional("__rt__async_io_close_source", "(usize)->i32"),
    additional("__rt__async_io_dup", "(i32)->i32"),
    additional("__rt__fd_lease_open", "(i32)->u64"),
    additional("__rt__fd_lease_acquire", "(u64)->i32"),
    additional("__rt__fd_lease_release", "(u64)->i32"),
    additional("__rt__fd_lease_close", "(u64)->i32"),
    additional("__rt__fd_lease_take", "(u64)->i32"),
    additional_with_escape(
        "__rt__async_io_pipe",
        "(*mut i32,*mut i32)->i32",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_with_escape(
        "__rt__async_io_read_source",
        "(usize,*mut u8,usize)->isize",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_with_escape(
        "__rt__async_io_write_source",
        "(usize,*const u8,usize)->isize",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_callback("__rt__executor_abort_rootless", "()->void"),
    additional_callback("__rt__executor_finish_rootless", "()->void"),
    additional_callback("__rt__executor_finish_main", "()->void"),
    additional_unix_blocking_with_escape(
        "__rt__env_current_dir",
        "(*mut *mut u8,*mut usize)->i32",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_blocking_with_escape(
        "__rt__env_get",
        "(string,*mut *mut u8,*mut usize,*mut bool)->i32",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_blocking_with_escape(
        "__rt__env_home_dir",
        "(*mut *mut u8,*mut usize)->i32",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_with_escape(
        "__rt__env_owned_bytes_free",
        "(*mut u8)->void",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_blocking_with_escape(
        "__rt__env_remove",
        "(string)->i32",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_blocking_with_escape(
        "__rt__env_set",
        "(string,string)->i32",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_blocking_with_escape(
        "__rt__env_set_current_dir",
        "(string)->i32",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_service_snapshot(
        "__rt__env_snapshot_at",
        "(usize,usize,*mut *const u8,*mut usize,*mut *const u8,*mut usize)->i32",
        false,
        &[
            RuntimeParamEscapeEffect::CaptureAndReturn,
            RuntimeParamEscapeEffect::NoCapture,
            RuntimeParamEscapeEffect::NoCapture,
            RuntimeParamEscapeEffect::NoCapture,
            RuntimeParamEscapeEffect::NoCapture,
            RuntimeParamEscapeEffect::NoCapture,
        ],
    ),
    additional_unix_with_escape(
        "__rt__env_snapshot_close",
        "(usize)->void",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_blocking_with_escape(
        "__rt__env_snapshot_open",
        "(*mut usize)->usize",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_blocking_with_escape(
        "__rt__env_temp_dir",
        "(*mut *mut u8,*mut usize)->i32",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_blocking_with_escape(
        "__rt__fs_canonicalize",
        "(string,*mut *mut u8,*mut usize)->i32",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_blocking_with_escape(
        "__rt__fs_copy",
        "(string,string,*mut u64)->i32",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_blocking_with_escape(
        "__rt__fs_create_temp_dir",
        "(string,string,*mut *mut u8,*mut usize)->i32",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_blocking_with_escape(
        "__rt__fs_dir_close",
        "(usize)->i32",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_blocking_with_escape(
        "__rt__fs_dir_open",
        "(string,*mut i32)->usize",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_service_snapshot(
        "__rt__fs_dir_read",
        "(usize,*mut *mut u8,*mut usize,*mut u8)->i32",
        true,
        &[
            RuntimeParamEscapeEffect::CaptureAndReturn,
            RuntimeParamEscapeEffect::NoCapture,
            RuntimeParamEscapeEffect::NoCapture,
            RuntimeParamEscapeEffect::NoCapture,
        ],
    ),
    additional_unix_blocking_with_escape(
        "__rt__fs_metadata",
        "(string,bool,*mut u8,*mut u64,*mut i64,*mut u32,*mut i64,*mut u32)->i32",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_with_escape(
        "__rt__fs_owned_bytes_free",
        "(*mut u8)->void",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_blocking_with_escape(
        "__rt__fs_remove_dir_all",
        "(string)->i32",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional(
        "__rt__existential_lookup_conformance",
        "(*const u8,*const u8)->*const u8",
    ),
    additional("__rt__hash_seed0", "()->u64"),
    additional("__rt__hash_seed1", "()->u64"),
    // ABI50 witness tables append a controller-convention byte per method.
    additional_unix_with_escape(
        "__rt__net_ip_snapshot_at",
        "(usize,usize,*mut u8,*mut u8)->i32",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    // HTTP shims own native snapshots; borrowed wire buffers never escape.
    additional_unix_with_escape(
        "__rt__http_header_valid",
        "(string,string)->bool",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_with_escape(
        "__rt__http_parse_head",
        "(*const u8,usize,usize,usize)->usize",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_with_escape(
        "__rt__http_check_head",
        "(*const u8,usize,usize,usize,*mut usize)->usize",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_with_escape(
        "__rt__http_chunk_size",
        "(string,*mut usize)->bool",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_with_escape(
        "__rt__http_snapshot_info",
        "(usize,usize)->usize",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_with_escape(
        "__rt__http_snapshot_bytes",
        "(usize,usize,*mut usize)->*const u8",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_with_escape(
        "__rt__http_snapshot_close",
        "(usize)->void",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_with_escape(
        "__rt__http_parse_response",
        "(*const u8,usize,usize,usize,bool)->usize",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_with_escape(
        "__rt__http_url",
        "(string,string)->usize",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_with_escape(
        "__rt__tls_config",
        "(bool,string,string)->usize",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_with_escape(
        "__rt__tls_session",
        "(usize,string)->usize",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_with_escape(
        "__rt__task_wake_after",
        "(u64,u32)->void",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_with_escape(
        "__rt__task_clear_wake",
        "()->void",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_with_escape(
        "__rt__task_hold_next_spawn",
        "()->void",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_with_escape(
        "__rt__task_group_discard_results",
        "(usize)->void",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_with_escape(
        "__rt__task_may_spin",
        "()->bool",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_with_escape(
        "__rt__task_should_stop_spinning",
        "()->bool",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_with_escape(
        "__rt__tls_close",
        "(usize)->void",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_with_escape(
        "__rt__tls_step",
        "(usize,u8,*mut u8,usize)->isize",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    // Maintained crypto backends borrow inputs; only native handles escape.
    additional_blocking_with_escape(
        "__rt__crypto_random",
        "(*mut u8,usize)->bool",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_blocking_with_escape(
        "__rt__crypto_digest",
        "(u8,*const u8,usize,*mut u8)->bool",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_blocking_with_escape(
        "__rt__crypto_hmac",
        "(u8,*const u8,usize,*const u8,usize,*mut u8)->bool",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_blocking_with_escape(
        "__rt__crypto_hmac_verify",
        "(u8,*const u8,usize,*const u8,usize,*const u8,usize)->bool",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_blocking_with_escape(
        "__rt__crypto_equal",
        "(*const u8,usize,*const u8,usize)->bool",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_callback_with_param_escape(
        "__rt__crypto_aead_new",
        "(*const u8,usize,*mut u8)->*mut u8",
        &[RuntimeParamEscapeEffect::NoCapture; 3],
    ),
    additional_blocking_with_escape(
        "__rt__crypto_aead_crypt",
        "(*const u8,bool,*const u8,usize,*const u8,usize)->usize",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_with_escape(
        "__rt__crypto_aead_close",
        "(*const u8)->void",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_with_escape(
        "__rt__crypto_output",
        "(usize,*mut usize,*mut u8)->*const u8",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_with_escape(
        "__rt__crypto_output_close",
        "(usize)->void",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_with_escape(
        "__rt__crypto_test_live_keys",
        "()->usize",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    // Resolver entry points synchronously copy wire strings/addresses before
    // libc can block. Neither input bytes nor caller output slots escape.
    // Result handles own independent Rust snapshots, not incoming storage.
    additional_unix_blocking_with_escape(
        "__rt__net_lookup_address",
        "(u8,*const u8,*mut usize,*mut u8,*mut i32,*mut i32)->usize",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_blocking_with_escape(
        "__rt__net_lookup_host",
        "(string,*mut usize,*mut u8,*mut i32,*mut i32)->usize",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix(
        "__rt__net_name_snapshot_at",
        "(usize,usize,*mut *const u8,*mut usize)->i32",
    ),
    additional_unix("__rt__net_snapshot_close", "(usize)->void"),
    additional_unix_blocking_with_escape(
        "__rt__open2",
        "(*const u8,i32)->i32",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_blocking_with_escape(
        "__rt__open3",
        "(*const u8,i32,i32)->i32",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    // These synchronous parsers finish reading the borrowed string and writing
    // the scalar output slot before returning; neither argument is retained.
    additional_with_escape(
        "__rt__parse_f32",
        "(string,*mut u32)->u8",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_with_escape(
        "__rt__parse_f64",
        "(string,*mut u64)->u8",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    // Panic entry points snapshot message/location bytes into native strings
    // before aborting or unwinding; borrowed wire headers are not retained.
    additional_callback_with_param_escape(
        "__rt__panic_abort",
        "(string)->never",
        &[RuntimeParamEscapeEffect::NoCapture],
    ),
    additional_callback("__rt__panic_abort_unwind", "(*mut u8)->never"),
    additional_callback("__rt__panic_abort_foreign", "(*mut u8)->never"),
    additional_callback_with_param_escape(
        "__rt__panic_unwind",
        "(string)->never",
        &[RuntimeParamEscapeEffect::NoCapture],
    ),
    additional_callback_with_param_escape(
        "__rt__panic_unwind_at",
        "(string,string,usize,usize)->never",
        &[
            RuntimeParamEscapeEffect::NoCapture,
            RuntimeParamEscapeEffect::NoCapture,
            RuntimeParamEscapeEffect::NoCapture,
            RuntimeParamEscapeEffect::NoCapture,
        ],
    ),
    additional_unix_with_escape(
        "__rt__process_child_abandon",
        "(usize)->void",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_with_escape(
        "__rt__process_child_kill",
        "(usize)->i32",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_with_escape(
        "__rt__process_child_pid",
        "(usize,*mut u32)->i32",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_with_escape(
        "__rt__process_child_try_wait",
        "(usize,*mut bool,*mut i32,*mut i32)->i32",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_blocking_with_escape(
        "__rt__process_child_wait",
        "(usize,*mut i32,*mut i32)->i32",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_with_escape(
        "__rt__process_command_arg",
        "(usize,string)->i32",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_with_escape(
        "__rt__process_command_close",
        "(usize)->void",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_with_escape(
        "__rt__process_command_current_dir",
        "(usize,string)->i32",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_with_escape(
        "__rt__process_command_env",
        "(usize,string,string)->i32",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_with_escape(
        "__rt__process_command_open",
        "(string,*mut i32)->usize",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_blocking_with_escape(
        "__rt__process_command_output",
        "(usize,bool,usize,*mut i32,*mut bool)->usize",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_blocking_with_escape(
        "__rt__process_command_spawn",
        "(usize,*mut usize,*mut i32,*mut i32,*mut i32)->i32",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_blocking_with_escape(
        "__rt__process_command_status",
        "(usize,*mut i32,*mut i32)->i32",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_with_escape(
        "__rt__process_command_stdio",
        "(usize,u8,u8,u8)->i32",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_with_escape(
        "__rt__process_output_close",
        "(usize)->void",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_service_snapshot(
        "__rt__process_output_stderr",
        "(usize,*mut *const u8,*mut usize)->i32",
        false,
        &[
            RuntimeParamEscapeEffect::CaptureAndReturn,
            RuntimeParamEscapeEffect::NoCapture,
            RuntimeParamEscapeEffect::NoCapture,
        ],
    ),
    additional_unix_with_escape(
        "__rt__process_output_status",
        "(usize,*mut i32,*mut i32)->i32",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_unix_service_snapshot(
        "__rt__process_output_stdout",
        "(usize,*mut *const u8,*mut usize)->i32",
        false,
        &[
            RuntimeParamEscapeEffect::CaptureAndReturn,
            RuntimeParamEscapeEffect::NoCapture,
            RuntimeParamEscapeEffect::NoCapture,
        ],
    ),
    additional_with_escape(
        "__rt__erased_register_openings",
        "(*const u8,usize)->void",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_with_escape(
        "__rt__erased_resolve_opening",
        "(*const u8,*const u8,*const u8)->*const u8",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    AdditionalRuntimeSymbol {
        symbol: "__rt__static_initialize",
        signature: "(*mut *mut u8,*mut u8,*const u8,*const u8)->void",
        availability: RuntimeSymbolAvailability::AllTargets,
        call_effect: RuntimeCallEffect::Callback,
        parameter_count: 4,
        param_escape_effects: AdditionalRuntimeParamEscapeEffects::PerParameter(&[
            RuntimeParamEscapeEffect::Capture,
            RuntimeParamEscapeEffect::Capture,
            RuntimeParamEscapeEffect::Capture,
            RuntimeParamEscapeEffect::NoCapture,
        ]),
    },
    additional_with_escape(
        "__rt__class_resolve_initializer",
        "(*const class_descriptor,*const u8,*const u8)->*const u8",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_param_escape(
        "__rt__class_register_generic_methods",
        "(*const generic_class_method,usize)->void",
        &[
            RuntimeParamEscapeEffect::Capture,
            RuntimeParamEscapeEffect::NoCapture,
        ],
    ),
    additional_with_escape(
        "__gc__string_copy",
        "(*const u8,usize)->*const u8",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    // A GC async frame is rooted by the runtime until its owner is dropped.
    additional_with_escape(
        "__gc__async_frame_allocate",
        "(*const u8)->*mut u8",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    // A collected owner releases its sync handle box once unreachable (G50).
    additional_with_escape(
        "__gc__sync_owner_new",
        "(*mut u8)->*mut u8",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    // Queued GC channel messages are rooted copies; the element descriptor is
    // static compiler metadata.
    additional_with_escape(
        "__gc__sync_channel_create",
        "(usize,u8,*const u8)->*mut u8",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    // Weak targets escape so referenced locals are heap-promoted; weak cells
    // themselves omit the target edge from their GC descriptor.
    additional_callback_with_param_escape(
        "__gc__weak_create",
        "(*const u8)->*mut u8",
        &[RuntimeParamEscapeEffect::Capture],
    ),
    additional_with_escape(
        "__gc__weak_value",
        "(*const u8)->*mut u8",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    // std::runtime::collect runs a collection, so callers need a stack map.
    additional_callback("__rt__gc_collect", "()->void"),
    additional_with_escape(
        "__rt__gc_stats",
        "(*mut u8)->void",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    // Foreign handles persistently root their target until deleted.
    additional_with_escape(
        "__gc__handle_new",
        "(*const u8)->usize",
        RuntimeParamEscapeEffect::Capture,
    ),
    additional_with_escape(
        "__gc__handle_value",
        "(usize)->*mut u8",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_with_escape(
        "__gc__handle_delete",
        "(usize)->bool",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    // GC managed sequences (G13/G14). Element descriptors are static
    // metadata; the old buffer of a growth stays reachable only through its
    // caller, and the published buffer is not retained by the runtime.
    additional_with_escape(
        "__gc__buffer_new",
        "(*const u8,usize)->*mut u8",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_with_escape(
        "__gc__dictionary_groups_new",
        "(*const u8,usize)->*mut u8",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_with_escape(
        "__gc__buffer_publish",
        "(*mut u8,*const u8,usize)->void",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_with_escape(
        "__gc__buffer_grow",
        "(*mut u8,*const u8,usize,usize)->*mut u8",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_callback_with_param_escape(
        "__rt__sync_handle_release",
        "(*mut u8)->void",
        &[RuntimeParamEscapeEffect::NoCapture],
    ),
    additional("__rt__sync_channel_close", "(*mut u8)->i32"),
    additional_callback_with_param_escape(
        "__rt__sync_channel_destroy",
        "(*mut u8)->i32",
        &[RuntimeParamEscapeEffect::NoCapture],
    ),
    additional_with_escape(
        "__rt__sync_channel_try_recv",
        "(*mut u8,*mut u8)->i32",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_with_escape(
        "__rt__sync_channel_try_send",
        "(*mut u8,*const u8)->i32",
        RuntimeParamEscapeEffect::NoCapture,
    ),
    additional_callback("__rt__sync_mutex_create", "()->*mut u8"),
    additional("__rt__sync_mutex_destroy", "(*mut u8)->i32"),
    additional("__rt__sync_mutex_try_lock", "(*mut u8)->i32"),
    additional("__rt__sync_mutex_unlock", "(*mut u8)->i32"),
    additional_callback("__rt__sync_rwlock_create", "()->*mut u8"),
    additional("__rt__sync_rwlock_destroy", "(*mut u8)->i32"),
    additional("__rt__sync_rwlock_try_read", "(*mut u8)->i32"),
    additional("__rt__sync_rwlock_try_write", "(*mut u8)->i32"),
    additional("__rt__sync_rwlock_unlock_read", "(*mut u8)->i32"),
    additional("__rt__sync_rwlock_unlock_write", "(*mut u8)->i32"),
    additional_callback("__rt__test_call_fn", "(fn()->void)->bool"),
    additional("__rt__test_panic_finish", "(u8,*const u8,usize)->void"),
    additional("__rt__test_panic_status", "(bool,bool,*const u8,usize)->u8"),
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
        call_effect: RuntimeCallEffect::Direct,
        parameter_count: runtime_signature_parameter_count(signature),
        param_escape_effects: AdditionalRuntimeParamEscapeEffects::Uniform(param_escape_effect),
    }
}

const fn additional_blocking_with_escape(
    symbol: &'static str,
    signature: &'static str,
    escape: RuntimeParamEscapeEffect,
) -> AdditionalRuntimeSymbol {
    let mut entry = additional_with_escape(symbol, signature, escape);
    entry.call_effect = RuntimeCallEffect::Blocking;
    entry
}

const fn additional_param_escape(
    symbol: &'static str,
    signature: &'static str,
    effects: &'static [RuntimeParamEscapeEffect],
) -> AdditionalRuntimeSymbol {
    AdditionalRuntimeSymbol {
        symbol,
        signature,
        availability: RuntimeSymbolAvailability::AllTargets,
        call_effect: RuntimeCallEffect::Direct,
        parameter_count: runtime_signature_parameter_count(signature),
        param_escape_effects: AdditionalRuntimeParamEscapeEffects::PerParameter(effects),
    }
}

const fn additional_callback(
    symbol: &'static str,
    signature: &'static str,
) -> AdditionalRuntimeSymbol {
    AdditionalRuntimeSymbol {
        symbol,
        signature,
        availability: RuntimeSymbolAvailability::AllTargets,
        call_effect: RuntimeCallEffect::Callback,
        parameter_count: runtime_signature_parameter_count(signature),
        param_escape_effects: AdditionalRuntimeParamEscapeEffects::Uniform(
            RuntimeParamEscapeEffect::CaptureAndReturn,
        ),
    }
}

const fn additional_callback_with_param_escape(
    symbol: &'static str,
    signature: &'static str,
    param_escape_effects: &'static [RuntimeParamEscapeEffect],
) -> AdditionalRuntimeSymbol {
    AdditionalRuntimeSymbol {
        symbol,
        signature,
        availability: RuntimeSymbolAvailability::AllTargets,
        call_effect: RuntimeCallEffect::Callback,
        parameter_count: runtime_signature_parameter_count(signature),
        param_escape_effects: AdditionalRuntimeParamEscapeEffects::PerParameter(
            param_escape_effects,
        ),
    }
}

const fn additional_unix(symbol: &'static str, signature: &'static str) -> AdditionalRuntimeSymbol {
    additional_unix_with_escape(
        symbol,
        signature,
        RuntimeParamEscapeEffect::CaptureAndReturn,
    )
}

/// Snapshot outputs lend runtime-owned bytes through raw output slots. Only
/// those slots are NoCapture; the opaque owning handle retains its conservative
/// effect, and no safe returned dependency or data provenance is implied.
const fn additional_unix_service_snapshot(
    symbol: &'static str,
    signature: &'static str,
    blocking: bool,
    effects: &'static [RuntimeParamEscapeEffect],
) -> AdditionalRuntimeSymbol {
    AdditionalRuntimeSymbol {
        symbol,
        signature,
        availability: RuntimeSymbolAvailability::Unix,
        call_effect: if blocking {
            RuntimeCallEffect::Blocking
        } else {
            RuntimeCallEffect::Direct
        },
        parameter_count: runtime_signature_parameter_count(signature),
        param_escape_effects: AdditionalRuntimeParamEscapeEffects::PerParameter(effects),
    }
}

const fn additional_unix_with_escape(
    symbol: &'static str,
    signature: &'static str,
    escape: RuntimeParamEscapeEffect,
) -> AdditionalRuntimeSymbol {
    AdditionalRuntimeSymbol {
        symbol,
        signature,
        availability: RuntimeSymbolAvailability::Unix,
        call_effect: RuntimeCallEffect::Direct,
        parameter_count: runtime_signature_parameter_count(signature),
        param_escape_effects: AdditionalRuntimeParamEscapeEffects::Uniform(escape),
    }
}

const fn additional_unix_blocking_with_escape(
    symbol: &'static str,
    signature: &'static str,
    escape: RuntimeParamEscapeEffect,
) -> AdditionalRuntimeSymbol {
    AdditionalRuntimeSymbol {
        symbol,
        signature,
        availability: RuntimeSymbolAvailability::Unix,
        call_effect: RuntimeCallEffect::Blocking,
        parameter_count: runtime_signature_parameter_count(signature),
        param_escape_effects: AdditionalRuntimeParamEscapeEffects::Uniform(escape),
    }
}

const fn runtime_signature_parameter_count(signature: &str) -> usize {
    let bytes = signature.as_bytes();
    if bytes.is_empty() || bytes[0] != b'(' {
        return 0;
    }

    let mut index = 1;
    let mut nested = 0usize;
    let mut count = 0usize;
    let mut has_parameter = false;
    while index < bytes.len() {
        match bytes[index] {
            b'(' => {
                nested += 1;
                has_parameter = true;
            }
            b')' if nested == 0 => {
                return if has_parameter { count + 1 } else { 0 };
            }
            b')' => nested -= 1,
            b',' if nested == 0 => count += 1,
            byte if !byte.is_ascii_whitespace() => has_parameter = true,
            _ => {}
        }
        index += 1;
    }
    0
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

pub fn call_effect_for_symbol(symbol: &str) -> Option<RuntimeCallEffect> {
    RuntimeAbiFunction::ALL
        .iter()
        .find_map(|function| (function.spec().symbol == symbol).then(|| function.call_effect()))
        .or_else(|| {
            ADDITIONAL_RUNTIME_SYMBOLS
                .iter()
                .find_map(|entry| (entry.symbol == symbol).then_some(entry.call_effect))
        })
}

/// The source/native admission check uses the same signature as artifact
/// manifests, rather than granting ownership permission from a familiar name.
pub fn signature_for_symbol(symbol: &str) -> Option<String> {
    RuntimeAbiFunction::ALL
        .iter()
        .find(|function| function.spec().symbol == symbol)
        .map(|function| function.spec().signature())
        .or_else(|| {
            ADDITIONAL_RUNTIME_SYMBOLS
                .iter()
                .find(|entry| entry.symbol == symbol)
                .map(|entry| entry.signature.to_owned())
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
                .and_then(|entry| entry.param_escape_effect(parameter))
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
        "__intrinsic_atomic_load" | "__intrinsic_atomic_swap" if parameter == 0 => E::Return,
        "__intrinsic_atomic_store" | "__intrinsic_atomic_swap" if parameter == 1 => E::Capture,
        "__intrinsic_atomic_compare_exchange" if parameter == 2 => E::Capture,
        "__intrinsic_atomic_load"
        | "__intrinsic_atomic_store"
        | "__intrinsic_atomic_swap"
        | "__intrinsic_atomic_compare_exchange"
        | "__intrinsic_atomic_add" => E::NoCapture,
        "__intrinsic_class_field_reference" => {
            if parameter == 0 {
                E::Return
            } else {
                E::NoCapture
            }
        }
        // Instantaneous accesses copy a trivial field out, or store a value
        // into the object; the handle slot is only observed for the call.
        "__intrinsic_class_field_read" | "__intrinsic_class_field_modify" => E::NoCapture,
        "__intrinsic_class_field_write" => {
            if parameter == 2 {
                E::Capture
            } else {
                E::NoCapture
            }
        }
        // Identity or pointer-producing operations return provenance from the
        // first argument without retaining it.
        "__intrinsic_black_box"
        | "__intrinsic_ref_project"
        | "__intrinsic_ref_project_mut"
        | "__intrinsic_array_read_unchecked"
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
        | "__intrinsic_string_data"
        | "__intrinsic_string_from_parts"
        | "__intrinsic_string_slice"
            if parameter == 0 =>
        {
            E::Return
        }

        // Typed writes publish the value argument into storage that may be
        // managed or otherwise outlive the call. The destination pointer is
        // only observed for the duration of the intrinsic.
        "__intrinsic_array_write_unchecked" if parameter == 2 => E::Capture,
        "__intrinsic_ptr_write" if parameter == 1 => E::Capture,

        // Raw memory operations synchronously copy bytes; they do not retain
        // either pointer value. Typed collection writes are responsible for
        // establishing any element escape before a buffer is copied or grown.
        "__intrinsic_memcpy" | "__intrinsic_memmove" => E::NoCapture,

        // Async constructors retain closures/state in their returned future
        // or task. Source-async placement is additionally conservative before
        // coroutine lowering.
        "__intrinsic_spawn_async" | "__intrinsic_blocking" if parameter == 0 => E::CaptureAndReturn,
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
        | "__intrinsic_ref_project"
        | "__intrinsic_ref_project_mut"
        | "__intrinsic_array_read_unchecked"
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
        | "__intrinsic_string_slice"
        | "__intrinsic_string_data"
        | "__intrinsic_spawn_async"
        | "__intrinsic_blocking"
        | "__intrinsic_task_group_spawn"
        | "__intrinsic_array_write_unchecked"
        | "__intrinsic_ptr_write"
        | "__intrinsic_memset"
        | "__intrinsic_string_len"
        | "__intrinsic_keep_alive"
        | "__intrinsic_size_of"
        | "__intrinsic_align_of"
        | "__intrinsic_maybe_uninit"
        | "__intrinsic_gc_value_descriptor"
        | "__intrinsic_task_output_descriptor"
        | "__intrinsic_env_argc"
        | "__intrinsic_env_argv"
        | "__intrinsic_rune_from_u32_unchecked"
        | "__intrinsic_cancel_task"
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
    // These operations load provenance through their first argument. String
    // views retain the bytes stored in &string, not the header slot; class
    // fields similarly retain the object rather than its handle slot.
    Some(
        if parameter == 0
            && matches!(
                symbol,
                "__intrinsic_ptr_read"
                    | "__intrinsic_string_data"
                    | "__intrinsic_string_slice"
                    | "__intrinsic_class_field_reference"
                    | "__intrinsic_atomic_load"
                    | "__intrinsic_atomic_swap"
            )
        {
            1
        } else {
            0
        },
    )
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
            function.call_effect().name(),
            spec.signature()
        );
    }
    for entry in ADDITIONAL_RUNTIME_SYMBOLS {
        let _ = writeln!(
            canonical,
            "{} [{}] [{}] {}",
            entry.symbol,
            entry.availability.name(),
            entry.call_effect.name(),
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
    fn dictionary_group_allocation_has_a_metadata_only_escape_contract() {
        let symbol = "__gc__dictionary_groups_new";
        assert_eq!(
            signature_for_symbol(symbol).as_deref(),
            Some("(*const u8,usize)->*mut u8")
        );
        assert_eq!(
            param_escape_effect_for_symbol(symbol, 0),
            Some(RuntimeParamEscapeEffect::NoCapture)
        );
        assert_eq!(
            param_escape_effect_for_symbol(symbol, 1),
            Some(RuntimeParamEscapeEffect::NoCapture)
        );
        assert_eq!(
            call_effect_for_symbol(symbol),
            Some(RuntimeCallEffect::Direct)
        );
    }

    #[test]
    fn native_sync_handle_release_can_run_callbacks_without_retaining_a_reference() {
        assert_eq!(
            call_effect_for_symbol("__rt__sync_handle_release"),
            Some(RuntimeCallEffect::Callback)
        );
        assert_eq!(
            param_escape_effect_for_symbol("__rt__sync_handle_release", 0),
            Some(RuntimeParamEscapeEffect::NoCapture)
        );
    }

    #[test]
    fn scalar_parsers_do_not_capture_their_inputs_or_output_slot() {
        for symbol in ["__rt__parse_f32", "__rt__parse_f64"] {
            assert_eq!(
                call_effect_for_symbol(symbol),
                Some(RuntimeCallEffect::Direct)
            );
            for index in 0..2 {
                assert_eq!(
                    param_escape_effect_for_symbol(symbol, index),
                    Some(RuntimeParamEscapeEffect::NoCapture)
                );
            }
            assert_eq!(param_escape_effect_for_symbol(symbol, 2), None);
        }
    }

    #[test]
    fn canonical_runtime_symbols_are_unique() {
        let symbols = required_symbols().collect::<Vec<_>>();
        let unique = symbols.iter().copied().collect::<HashSet<_>>();
        assert_eq!(symbols.len(), unique.len());
    }

    #[test]
    fn every_runtime_symbol_has_an_explicit_call_effect() {
        for symbol in required_symbols() {
            assert!(
                call_effect_for_symbol(symbol).is_some(),
                "missing call effect for {symbol}"
            );
        }
        assert_eq!(call_effect_for_symbol("__gc__alloc"), None);
        assert_eq!(
            call_effect_for_symbol("__rt__hash_seed0"),
            Some(RuntimeCallEffect::Direct)
        );
        assert_eq!(
            call_effect_for_symbol("__rt__task_spawn_with_metadata"),
            Some(RuntimeCallEffect::Callback),
            "spawn may enter Taro callbacks and needs diagnostic call metadata"
        );
        for symbol in [
            "__rt__task_group_create",
            "__rt__task_group_spawn_with_metadata",
        ] {
            assert_eq!(
                call_effect_for_symbol(symbol),
                Some(RuntimeCallEffect::Callback),
                "group operations may enter Taro callbacks; preserve the diagnostic call boundary"
            );
        }
        assert_eq!(call_effect_for_symbol("__rt__test_gc_probe_create"), None);
        assert_eq!(
            call_effect_for_symbol("__rt__test_gc_collect_probe_is_live"),
            None
        );
        assert_eq!(
            call_effect_for_symbol("__rt__open2"),
            Some(RuntimeCallEffect::Blocking)
        );
        assert_eq!(call_effect_for_symbol("__rt__missing"), None);
    }

    #[test]
    fn channel_cleanup_and_transfer_have_distinct_callback_boundaries() {
        assert_eq!(
            call_effect_for_symbol("__rt__sync_channel_destroy"),
            Some(RuntimeCallEffect::Callback)
        );
        for symbol in ["__rt__sync_channel_try_send", "__rt__sync_channel_try_recv"] {
            assert_eq!(
                call_effect_for_symbol(symbol),
                Some(RuntimeCallEffect::Direct)
            );
            for index in 0..2 {
                assert_eq!(
                    param_escape_effect_for_symbol(symbol, index),
                    Some(RuntimeParamEscapeEffect::NoCapture)
                );
            }
        }
    }

    #[test]
    fn resolver_snapshots_do_not_retain_caller_buffers_or_claim_owned_name_bytes() {
        for (symbol, count, effect) in [
            ("__rt__net_lookup_host", 5, RuntimeCallEffect::Blocking),
            ("__rt__net_lookup_address", 6, RuntimeCallEffect::Blocking),
            ("__rt__net_ip_snapshot_at", 4, RuntimeCallEffect::Direct),
        ] {
            assert_eq!(call_effect_for_symbol(symbol), Some(effect));
            for parameter in 0..count {
                assert_eq!(
                    param_escape_effect_for_symbol(symbol, parameter),
                    Some(RuntimeParamEscapeEffect::NoCapture)
                );
            }
            assert_eq!(param_escape_effect_for_symbol(symbol, count), None);
        }
        // This returns a pointer into the snapshot through an output slot.
        // Do not misrepresent its bytes as independently owned or extend the
        // synchronous resolver audit to retained asynchronous I/O buffers.
        assert_ne!(
            param_escape_effect_for_symbol("__rt__net_name_snapshot_at", 0),
            Some(RuntimeParamEscapeEffect::NoCapture)
        );
        assert_ne!(
            param_escape_effect_for_symbol("__rt__async_rwlock_write", 0),
            Some(RuntimeParamEscapeEffect::NoCapture)
        );
    }

    #[test]
    fn atomic_reference_publication_captures_only_the_stored_target() {
        for (symbol, target) in [
            ("__intrinsic_atomic_store", 1),
            ("__intrinsic_atomic_swap", 1),
            ("__intrinsic_atomic_compare_exchange", 2),
        ] {
            assert_eq!(
                intrinsic_param_escape_effect(symbol, 0),
                Some(if symbol == "__intrinsic_atomic_swap" {
                    RuntimeParamEscapeEffect::Return
                } else {
                    RuntimeParamEscapeEffect::NoCapture
                })
            );
            assert_eq!(
                intrinsic_param_escape_effect(symbol, target),
                Some(RuntimeParamEscapeEffect::Capture)
            );
        }
        assert_eq!(
            intrinsic_param_escape_effect("__intrinsic_atomic_compare_exchange", 1),
            Some(RuntimeParamEscapeEffect::NoCapture)
        );
    }

    #[test]
    fn crypto_primitives_publish_blocking_roots_without_capturing_managed_bytes() {
        assert_eq!(
            call_effect_for_symbol("__rt__crypto_aead_new"),
            Some(RuntimeCallEffect::Callback)
        );
        for parameter in 0..3 {
            assert_eq!(
                param_escape_effect_for_symbol("__rt__crypto_aead_new", parameter),
                Some(RuntimeParamEscapeEffect::NoCapture)
            );
        }

        for (symbol, count) in [
            ("__rt__crypto_random", 2),
            ("__rt__crypto_digest", 4),
            ("__rt__crypto_hmac", 6),
            ("__rt__crypto_hmac_verify", 7),
            ("__rt__crypto_equal", 4),
            ("__rt__crypto_aead_crypt", 6),
        ] {
            assert_eq!(
                call_effect_for_symbol(symbol),
                Some(RuntimeCallEffect::Blocking)
            );
            for parameter in 0..count {
                assert_eq!(
                    param_escape_effect_for_symbol(symbol, parameter),
                    Some(RuntimeParamEscapeEffect::NoCapture)
                );
            }
            assert_eq!(param_escape_effect_for_symbol(symbol, count), None);
        }
    }

    #[test]
    fn http_transport_and_parser_only_borrow_caller_storage() {
        for (symbol, parameters) in [
            ("__rt__http_parse_response", 5),
            ("__rt__http_url", 2),
            ("__rt__tls_step", 4),
            ("__rt__tls_config", 3),
            ("__rt__tls_session", 2),
            ("__rt__http_parse_head", 4),
            ("__rt__http_check_head", 5),
            ("__rt__http_header_valid", 2),
            ("__rt__http_chunk_size", 2),
            ("__rt__http_snapshot_bytes", 3),
        ] {
            for parameter in 0..parameters {
                assert_eq!(
                    param_escape_effect_for_symbol(symbol, parameter),
                    Some(RuntimeParamEscapeEffect::NoCapture)
                );
            }
            assert_eq!(param_escape_effect_for_symbol(symbol, parameters), None);
        }
        assert_eq!(
            call_effect_for_symbol("__rt__tls_step"),
            Some(RuntimeCallEffect::Direct)
        );
        assert_eq!(
            call_effect_for_symbol("__rt__http_parse_head"),
            Some(RuntimeCallEffect::Direct)
        );
    }

    #[test]
    fn panic_messages_are_snapshotted_before_unwinding() {
        // These entry points copy both message and location bytes into owned
        // runtime strings before raising. No incoming wire storage escapes.
        for (symbol, parameters) in [
            ("__rt__panic_unwind", 1),
            ("__rt__panic_abort", 1),
            ("__rt__panic_unwind_at", 4),
        ] {
            assert_eq!(
                call_effect_for_symbol(symbol),
                Some(RuntimeCallEffect::Callback)
            );
            for parameter in 0..parameters {
                assert_eq!(
                    param_escape_effect_for_symbol(symbol, parameter),
                    Some(RuntimeParamEscapeEffect::NoCapture)
                );
            }
            assert_eq!(param_escape_effect_for_symbol(symbol, parameters), None);
        }
        // An exception object has a different ownership contract; do not
        // extend the message snapshot rule to arbitrary unwind payloads.
        assert_ne!(
            param_escape_effect_for_symbol("__rt__panic_abort_unwind", 0),
            Some(RuntimeParamEscapeEffect::NoCapture)
        );
    }

    #[test]
    fn suspended_frame_cancellation_keeps_callback_roots_without_retaining_inputs() {
        let symbol = "__rt__async_cancel_frame";
        assert_eq!(
            call_effect_for_symbol(symbol),
            Some(RuntimeCallEffect::Callback)
        );
        for parameter in 0..2 {
            assert_eq!(
                param_escape_effect_for_symbol(symbol, parameter),
                Some(RuntimeParamEscapeEffect::NoCapture)
            );
        }
    }

    #[test]
    fn static_initialization_preserves_roots_and_retains_only_process_long_inputs() {
        let symbol = "__rt__static_initialize";
        assert_eq!(
            call_effect_for_symbol(symbol),
            Some(RuntimeCallEffect::Callback)
        );
        assert_eq!(
            ADDITIONAL_RUNTIME_SYMBOLS
                .iter()
                .find(|entry| entry.symbol == symbol)
                .unwrap()
                .signature,
            "(*mut *mut u8,*mut u8,*const u8,*const u8)->void"
        );
        for parameter in 0..3 {
            assert_eq!(
                param_escape_effect_for_symbol(symbol, parameter),
                Some(RuntimeParamEscapeEffect::Capture)
            );
        }
        assert_eq!(
            param_escape_effect_for_symbol(symbol, 3),
            Some(RuntimeParamEscapeEffect::NoCapture)
        );
    }

    #[test]
    fn retired_tracing_entries_are_not_runtime_abi_operations() {
        for symbol in [
            "__rt__cleanup_register",
            "__rt__cleanup_cancel",
            "__gc__alloc",
            "__gc__collect",
            "__rt__weak_create",
            "__rt__weak_value",
            "__rt__gc_enter_blocking",
        ] {
            assert_eq!(call_effect_for_symbol(symbol), None);
            assert_eq!(signature_for_symbol(symbol), None);
            assert!(!required_symbols().any(|known| known == symbol));
        }
    }

    #[test]
    fn string_views_return_backing_dependencies_without_capturing_headers() {
        for (name, count, deref) in [
            ("__intrinsic_string_from_parts", 2, 0),
            ("__intrinsic_string_slice", 3, 1),
            ("__intrinsic_string_data", 1, 1),
        ] {
            assert_eq!(intrinsic_return_deref(name, 0), Some(deref));
            for parameter in 0..count {
                assert_eq!(
                    intrinsic_param_escape_effect(name, parameter),
                    Some(if parameter == 0 {
                        RuntimeParamEscapeEffect::Return
                    } else {
                        RuntimeParamEscapeEffect::NoCapture
                    })
                );
            }
        }
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
            for parameter in 0..entry.parameter_count {
                assert!(
                    param_escape_effect_for_symbol(entry.symbol, parameter).is_some(),
                    "missing parameter {parameter} escape effect for {}",
                    entry.symbol
                );
            }
            assert_eq!(
                param_escape_effect_for_symbol(entry.symbol, entry.parameter_count),
                None,
                "additional runtime entries must reject out-of-range parameters"
            );
        }
        assert_eq!(param_escape_effect_for_symbol("__rt__keep_alive", 0), None);
        assert_eq!(param_escape_effect_for_symbol("__gc__grow_buf", 0), None);
        assert_eq!(param_escape_effect_for_symbol("__gc__grow_buf", 1), None);
        assert_eq!(param_escape_effect_for_symbol("__rt__missing", 0), None);
    }

    #[test]
    fn intrinsic_escape_effects_distinguish_aliases_stores_and_scalars() {
        assert_eq!(
            intrinsic_param_escape_effect("__intrinsic_ptr_add", 0),
            Some(RuntimeParamEscapeEffect::Return)
        );
        assert_eq!(
            intrinsic_param_escape_effect("__intrinsic_ptr_add", 1),
            Some(RuntimeParamEscapeEffect::NoCapture)
        );
        assert_eq!(
            intrinsic_param_escape_effect("__intrinsic_ptr_write", 1),
            Some(RuntimeParamEscapeEffect::Capture)
        );
        assert_eq!(
            intrinsic_param_escape_effect("__intrinsic_memcpy", 1),
            Some(RuntimeParamEscapeEffect::NoCapture)
        );
        assert_eq!(
            intrinsic_param_escape_effect("__intrinsic_checked_add", 0),
            Some(RuntimeParamEscapeEffect::NoCapture)
        );
        assert_eq!(intrinsic_return_deref("__intrinsic_ptr_read", 0), Some(1));
        assert_eq!(
            intrinsic_return_deref("__intrinsic_class_field_reference", 0),
            Some(1)
        );
        assert_eq!(
            intrinsic_param_escape_effect("__intrinsic_not_registered", 0),
            None
        );
    }

    #[test]
    fn fingerprint_changes_with_revision_or_signature_text() {
        assert_eq!(fingerprint().len(), 64);
        assert_ne!(fingerprint(), blake3::hash(b"").to_hex().to_string());
    }

    #[test]
    fn spawned_output_descriptors_are_typed_without_capturing_the_header_address() {
        use RuntimeAbiFunction as F;
        use RuntimeAbiType as T;
        use RuntimeParamEscapeEffect as E;
        assert_eq!(F::Blocking.spec().inputs, &[T::AsyncHandle, T::ConstU8Ptr]);
        assert_eq!(F::Blocking.param_escape_effect(1), Some(E::NoCapture));
        assert_eq!(F::Spawn.spec().inputs[1], T::ConstU8Ptr);
        assert_eq!(F::Spawn.param_escape_effect(1), Some(E::NoCapture));
        assert_eq!(F::Spawn.param_escape_effect(0), Some(E::Capture));
        assert_eq!(F::TaskGroupSpawn.spec().inputs[2], T::ConstU8Ptr);
        assert_eq!(F::TaskGroupSpawn.param_escape_effect(2), Some(E::NoCapture));
        assert_eq!(
            intrinsic_param_escape_effect("__intrinsic_task_output_descriptor", 0),
            Some(E::NoCapture)
        );
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
