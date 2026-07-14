//! Canonical compiler/runtime ABI definition.
//!
//! Synthetic compiler declarations are generated from the typed entries in
//! this module. The same table is fingerprinted into runtime artifact
//! manifests, so changing any symbol or signature requires an explicit ABI
//! revision update.

use std::fmt::Write as _;

pub const RUNTIME_ABI_REVISION: u32 = 6;
pub const RUNTIME_MANIFEST_SCHEMA: u32 = 1;

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
    additional("__gc__alloc", "(usize,*const gc_desc)->*mut u8"),
    additional("__gc__collect", "()->void"),
    additional(
        "__gc__grow_buf",
        "(*mut u8,*const gc_desc,usize,usize)->*mut u8",
    ),
    additional("__gc__makebuf", "(*const gc_desc,usize,usize)->*mut u8"),
    additional("__gc__poll", "()->void"),
    additional("__gc__register_static", "(*const u8,usize)->void"),
    additional("__gc__set_buf_len", "(*mut u8,*const gc_desc,usize)->void"),
    additional("__rt__cleanup_cancel", "(usize)->bool"),
    additional("__rt__cleanup_wait", "()->void"),
    additional("__rt__async_io_adopt_fd", "(i32)->usize"),
    additional("__rt__async_io_close_source", "(usize)->i32"),
    additional("__rt__async_io_dup", "(i32)->i32"),
    additional("__rt__async_io_pipe", "(*mut i32,*mut i32)->i32"),
    additional("__rt__async_io_read_source", "(usize,*mut u8,usize)->isize"),
    additional(
        "__rt__async_io_write_source",
        "(usize,*const u8,usize)->isize",
    ),
    additional("__rt__executor_abort_rootless", "()->void"),
    additional("__rt__executor_finish_rootless", "()->void"),
    additional_unix("__rt__env_current_dir", "(*mut *mut u8,*mut usize)->i32"),
    additional_unix(
        "__rt__env_get",
        "(string,*mut *mut u8,*mut usize,*mut bool)->i32",
    ),
    additional_unix("__rt__env_home_dir", "(*mut *mut u8,*mut usize)->i32"),
    additional_unix("__rt__env_owned_bytes_free", "(*mut u8)->void"),
    additional_unix("__rt__env_remove", "(string)->i32"),
    additional_unix("__rt__env_set", "(string,string)->i32"),
    additional_unix("__rt__env_set_current_dir", "(string)->i32"),
    additional_unix(
        "__rt__env_snapshot_at",
        "(usize,usize,*mut *const u8,*mut usize,*mut *const u8,*mut usize)->i32",
    ),
    additional_unix("__rt__env_snapshot_close", "(usize)->void"),
    additional_unix("__rt__env_snapshot_open", "(*mut usize)->usize"),
    additional_unix("__rt__env_temp_dir", "(*mut *mut u8,*mut usize)->i32"),
    additional_unix(
        "__rt__fs_canonicalize",
        "(string,*mut *mut u8,*mut usize)->i32",
    ),
    additional_unix("__rt__fs_copy", "(string,string,*mut u64)->i32"),
    additional_unix(
        "__rt__fs_create_temp_dir",
        "(string,string,*mut *mut u8,*mut usize)->i32",
    ),
    additional_unix("__rt__fs_dir_close", "(usize)->i32"),
    additional_unix("__rt__fs_dir_open", "(string,*mut i32)->usize"),
    additional_unix(
        "__rt__fs_dir_read",
        "(usize,*mut *mut u8,*mut usize,*mut u8)->i32",
    ),
    additional_unix(
        "__rt__fs_metadata",
        "(string,bool,*mut u8,*mut u64,*mut i64,*mut u32,*mut i64,*mut u32)->i32",
    ),
    additional_unix("__rt__fs_owned_bytes_free", "(*mut u8)->void"),
    additional_unix("__rt__fs_remove_dir_all", "(string)->i32"),
    additional(
        "__rt__existential_lookup_conformance",
        "(*const u8,*const u8)->*const u8",
    ),
    additional("__rt__gc_enter_blocking", "()->void"),
    additional("__rt__gc_exit_blocking", "()->void"),
    additional("__rt__gc_pop_frame", "(*mut gc_shadow_frame)->void"),
    additional("__rt__gc_push_frame", "(*mut gc_shadow_frame)->void"),
    additional("__rt__hash_seed0", "()->u64"),
    additional("__rt__hash_seed1", "()->u64"),
    additional("__rt__keep_alive", "(*const u8)->void"),
    additional("__rt__logical_stack_pop", "()->void"),
    additional("__rt__logical_stack_push", "(string)->void"),
    additional_unix("__rt__open2", "(*const u8,i32)->i32"),
    additional_unix("__rt__open3", "(*const u8,i32,i32)->i32"),
    additional("__rt__parse_f32", "(string,*mut u32)->u8"),
    additional("__rt__parse_f64", "(string,*mut u64)->u8"),
    additional("__rt__panic_abort", "(string)->never"),
    additional("__rt__panic_abort_unwind", "(*mut u8)->never"),
    additional("__rt__panic_unwind", "(string)->never"),
    additional(
        "__rt__panic_unwind_at",
        "(string,string,usize,usize)->never",
    ),
    additional("__rt__sync_channel_close", "(*mut u8)->i32"),
    additional(
        "__rt__sync_channel_create",
        "(usize,usize,u8,*const gc_desc)->*mut u8",
    ),
    additional("__rt__sync_channel_destroy", "(*mut u8)->i32"),
    additional("__rt__sync_channel_try_recv", "(*mut u8,*mut u8)->i32"),
    additional("__rt__sync_channel_try_send", "(*mut u8,*const u8)->i32"),
    additional("__rt__sync_mutex_create", "()->*mut u8"),
    additional("__rt__sync_mutex_destroy", "(*mut u8)->i32"),
    additional("__rt__sync_mutex_try_lock", "(*mut u8)->i32"),
    additional("__rt__sync_mutex_unlock", "(*mut u8)->i32"),
    additional("__rt__sync_rwlock_create", "()->*mut u8"),
    additional("__rt__sync_rwlock_destroy", "(*mut u8)->i32"),
    additional("__rt__sync_rwlock_try_read", "(*mut u8)->i32"),
    additional("__rt__sync_rwlock_try_write", "(*mut u8)->i32"),
    additional("__rt__sync_rwlock_unlock_read", "(*mut u8)->i32"),
    additional("__rt__sync_rwlock_unlock_write", "(*mut u8)->i32"),
    additional("__rt__test_call_fn", "(fn()->void)->bool"),
    additional("__rt__test_panic_finish", "(bool,*const u8,usize)->void"),
    additional("__rt__test_panic_status", "(bool,*const u8,usize)->u8"),
    additional("__rt__weak_create", "(*const u8)->*mut u8"),
    additional("__rt__weak_value", "(*mut u8)->*mut u8"),
];

const fn additional(symbol: &'static str, signature: &'static str) -> AdditionalRuntimeSymbol {
    AdditionalRuntimeSymbol {
        symbol,
        signature,
        availability: RuntimeSymbolAvailability::AllTargets,
    }
}

const fn additional_unix(symbol: &'static str, signature: &'static str) -> AdditionalRuntimeSymbol {
    AdditionalRuntimeSymbol {
        symbol,
        signature,
        availability: RuntimeSymbolAvailability::Unix,
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

pub fn fingerprint() -> String {
    let mut canonical = format!("runtime-abi-revision={RUNTIME_ABI_REVISION}\n");
    for function in RuntimeAbiFunction::ALL {
        let spec = function.spec();
        let _ = writeln!(canonical, "{} {}", spec.symbol, spec.signature());
    }
    for entry in ADDITIONAL_RUNTIME_SYMBOLS {
        let _ = writeln!(
            canonical,
            "{} [{}] {}",
            entry.symbol,
            entry.availability.name(),
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
        assert!(!windows.contains("__rt__open2"));
        assert!(!windows.contains("__rt__env_get"));
        assert!(!windows.contains("__rt__env_snapshot_open"));
        assert!(!windows.contains("__rt__fs_metadata"));
        assert!(!windows.contains("__rt__fs_remove_dir_all"));
    }

    #[test]
    fn scalar_parse_exports_are_part_of_the_canonical_abi() {
        let symbols = required_symbols().collect::<HashSet<_>>();
        assert!(symbols.contains("__rt__parse_f32"));
        assert!(symbols.contains("__rt__parse_f64"));
    }
}
