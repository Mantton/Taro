//! Stable Unix name-resolution shims for the Taro standard library.
//!
//! `getaddrinfo` and `getnameinfo` return pointers whose ownership and layout
//! are platform-specific. This module copies their results into bounded Rust
//! snapshots before exposing opaque handles across the runtime ABI.

use crate::env::lock_process_state;
use crate::panic_unwind::RtString;
use std::ffi::{CStr, CString};
use std::io;
use std::mem::{self, size_of};
use std::ptr;

const RESOLVE_OK: u8 = 0;
const RESOLVE_NOT_FOUND: u8 = 1;
const RESOLVE_TEMPORARY: u8 = 2;
const RESOLVE_INVALID_INPUT: u8 = 3;
const RESOLVE_UNSUPPORTED: u8 = 4;
const RESOLVE_RESOURCE_EXHAUSTED: u8 = 5;
const RESOLVE_SYSTEM: u8 = 6;
const RESOLVE_UNEXPECTED: u8 = 7;

const ADDRESS_FAMILY_IPV4: u8 = 4;
const ADDRESS_FAMILY_IPV6: u8 = 6;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ResolveFailure {
    kind: u8,
    resolver_code: i32,
    system_code: i32,
}

impl ResolveFailure {
    const fn new(kind: u8, resolver_code: i32, system_code: i32) -> Self {
        Self {
            kind,
            resolver_code,
            system_code,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct AddressEntry {
    family: u8,
    octets: [u8; 16],
}

enum ResolverSnapshot {
    Addresses(Vec<AddressEntry>),
    Names(Vec<Vec<u8>>),
}

struct AddrInfoGuard(*mut libc::addrinfo);

impl Drop for AddrInfoGuard {
    fn drop(&mut self) {
        if !self.0.is_null() {
            unsafe { libc::freeaddrinfo(self.0) };
        }
    }
}

fn input_c_string(value: RtString, empty_kind: u8) -> Result<CString, ResolveFailure> {
    if value.len > 0 && value.ptr.is_null() {
        return Err(ResolveFailure::new(RESOLVE_INVALID_INPUT, 0, 0));
    }
    let bytes = if value.len == 0 {
        &[][..]
    } else {
        unsafe { std::slice::from_raw_parts(value.ptr, value.len) }
    };
    if bytes.is_empty() {
        return Err(ResolveFailure::new(empty_kind, 0, 0));
    }
    CString::new(bytes).map_err(|_| ResolveFailure::new(RESOLVE_INVALID_INPUT, 0, 0))
}

fn system_error_code() -> i32 {
    io::Error::last_os_error()
        .raw_os_error()
        .unwrap_or(libc::EIO)
}

fn classify_resolver_error(code: i32, system_code: i32) -> ResolveFailure {
    if code == libc::EAI_NONAME {
        return ResolveFailure::new(RESOLVE_NOT_FOUND, code, 0);
    }
    #[cfg(any(
        target_os = "android",
        target_os = "ios",
        target_os = "linux",
        target_os = "macos",
        target_os = "netbsd",
        target_os = "openbsd",
        target_os = "solaris",
        target_os = "illumos"
    ))]
    if code == libc::EAI_NODATA {
        return ResolveFailure::new(RESOLVE_NOT_FOUND, code, 0);
    }
    if code == libc::EAI_AGAIN {
        return ResolveFailure::new(RESOLVE_TEMPORARY, code, 0);
    }
    if code == libc::EAI_MEMORY || code == libc::EAI_OVERFLOW {
        return ResolveFailure::new(RESOLVE_RESOURCE_EXHAUSTED, code, 0);
    }
    if code == libc::EAI_SYSTEM {
        return ResolveFailure::new(RESOLVE_SYSTEM, code, system_code);
    }
    if code == libc::EAI_FAMILY {
        return ResolveFailure::new(RESOLVE_UNSUPPORTED, code, 0);
    }
    if code == libc::EAI_BADFLAGS || code == libc::EAI_SERVICE || code == libc::EAI_SOCKTYPE {
        // These errors would describe the runtime-owned hints rather than user
        // hostname text, so classify them as an internal contract failure.
        return ResolveFailure::new(RESOLVE_UNEXPECTED, code, 0);
    }
    ResolveFailure::new(RESOLVE_UNEXPECTED, code, 0)
}

fn write_failure(
    failure: ResolveFailure,
    kind_out: *mut u8,
    resolver_code_out: *mut i32,
    system_code_out: *mut i32,
) {
    unsafe {
        kind_out.write(failure.kind);
        resolver_code_out.write(failure.resolver_code);
        system_code_out.write(failure.system_code);
    }
}

fn prepare_outputs(
    len_out: *mut usize,
    kind_out: *mut u8,
    resolver_code_out: *mut i32,
    system_code_out: *mut i32,
) -> bool {
    if len_out.is_null()
        || kind_out.is_null()
        || resolver_code_out.is_null()
        || system_code_out.is_null()
    {
        return false;
    }
    unsafe {
        len_out.write(0);
        kind_out.write(RESOLVE_OK);
        resolver_code_out.write(0);
        system_code_out.write(0);
    }
    true
}

fn lookup_host(value: RtString) -> Result<Vec<AddressEntry>, ResolveFailure> {
    // Match Go's LookupHost contract: an empty name is a typed not-found
    // result, while an embedded NUL is invalid input rather than truncation.
    let host = input_c_string(value, RESOLVE_NOT_FOUND)?;
    let mut hints: libc::addrinfo = unsafe { mem::zeroed() };
    hints.ai_family = libc::AF_UNSPEC;
    // Restrict the query to one socket type so libc does not repeat every
    // address once per supported transport protocol.
    hints.ai_socktype = libc::SOCK_STREAM;

    let mut head = ptr::null_mut();
    let (code, system_code) = {
        // Some libc resolver paths inspect process-global environment state.
        // Coordinate with std.env mutation only for the native call; returned
        // addrinfo nodes are independently owned until freeaddrinfo.
        let _guard = lock_process_state();
        let code = unsafe { libc::getaddrinfo(host.as_ptr(), ptr::null(), &hints, &mut head) };
        let system_code = if code == libc::EAI_SYSTEM {
            system_error_code()
        } else {
            0
        };
        (code, system_code)
    };
    if code != 0 {
        return Err(classify_resolver_error(code, system_code));
    }
    let _guard = AddrInfoGuard(head);

    let mut entries = Vec::new();
    let mut current = head;
    while !current.is_null() {
        let info = unsafe { &*current };
        let entry = if info.ai_family == libc::AF_INET
            && !info.ai_addr.is_null()
            && (info.ai_addrlen as usize) >= size_of::<libc::sockaddr_in>()
        {
            let address = unsafe { &*(info.ai_addr.cast::<libc::sockaddr_in>()) };
            let mut octets = [0_u8; 16];
            octets[..4].copy_from_slice(&address.sin_addr.s_addr.to_ne_bytes());
            Some(AddressEntry {
                family: ADDRESS_FAMILY_IPV4,
                octets,
            })
        } else if info.ai_family == libc::AF_INET6
            && !info.ai_addr.is_null()
            && (info.ai_addrlen as usize) >= size_of::<libc::sockaddr_in6>()
        {
            let address = unsafe { &*(info.ai_addr.cast::<libc::sockaddr_in6>()) };
            Some(AddressEntry {
                family: ADDRESS_FAMILY_IPV6,
                octets: address.sin6_addr.s6_addr,
            })
        } else {
            None
        };

        if let Some(entry) = entry {
            // Preserve the first occurrence of each OS result. This keeps libc
            // preference order without exposing duplicate protocol records.
            if !entries.contains(&entry) {
                entries.push(entry);
            }
        }
        current = info.ai_next;
    }

    if entries.is_empty() {
        return Err(ResolveFailure::new(RESOLVE_NOT_FOUND, 0, 0));
    }
    Ok(entries)
}

unsafe fn copy_address(address: *const u8, len: usize) -> Result<[u8; 16], ResolveFailure> {
    if address.is_null() {
        return Err(ResolveFailure::new(RESOLVE_INVALID_INPUT, 0, 0));
    }
    let mut octets = [0_u8; 16];
    unsafe { ptr::copy_nonoverlapping(address, octets.as_mut_ptr(), len) };
    Ok(octets)
}

fn socket_address_storage<T>(address: &T) -> libc::sockaddr_storage {
    debug_assert!(size_of::<T>() <= size_of::<libc::sockaddr_storage>());
    let mut storage: libc::sockaddr_storage = unsafe { mem::zeroed() };
    unsafe {
        ptr::copy_nonoverlapping(
            (address as *const T).cast::<u8>(),
            (&mut storage as *mut libc::sockaddr_storage).cast::<u8>(),
            size_of::<T>(),
        )
    };
    storage
}

fn lookup_address(family: u8, address: *const u8) -> Result<Vec<Vec<u8>>, ResolveFailure> {
    let mut host = vec![0_u8; libc::NI_MAXHOST as usize];
    let (socket_address, socket_address_len) = match family {
        ADDRESS_FAMILY_IPV4 => {
            let octets = unsafe { copy_address(address, 4)? };
            let mut socket: libc::sockaddr_in = unsafe { mem::zeroed() };
            socket.sin_family = libc::AF_INET as libc::sa_family_t;
            #[cfg(any(
                target_os = "aix",
                target_os = "freebsd",
                target_os = "haiku",
                target_os = "ios",
                target_os = "macos",
                target_os = "netbsd",
                target_os = "openbsd"
            ))]
            {
                socket.sin_len = size_of::<libc::sockaddr_in>() as u8;
            }
            socket.sin_addr = libc::in_addr {
                s_addr: u32::from_ne_bytes(octets[..4].try_into().expect("fixed IPv4 width")),
            };
            let storage = socket_address_storage(&socket);
            (storage, size_of::<libc::sockaddr_in>() as libc::socklen_t)
        }
        ADDRESS_FAMILY_IPV6 => {
            let octets = unsafe { copy_address(address, 16)? };
            let mut socket: libc::sockaddr_in6 = unsafe { mem::zeroed() };
            socket.sin6_family = libc::AF_INET6 as libc::sa_family_t;
            #[cfg(any(
                target_os = "aix",
                target_os = "freebsd",
                target_os = "haiku",
                target_os = "ios",
                target_os = "macos",
                target_os = "netbsd",
                target_os = "openbsd"
            ))]
            {
                socket.sin6_len = size_of::<libc::sockaddr_in6>() as u8;
            }
            socket.sin6_addr = libc::in6_addr { s6_addr: octets };
            let storage = socket_address_storage(&socket);
            (storage, size_of::<libc::sockaddr_in6>() as libc::socklen_t)
        }
        _ => return Err(ResolveFailure::new(RESOLVE_UNSUPPORTED, 0, 0)),
    };

    let (code, system_code) = {
        let _guard = lock_process_state();
        let code = unsafe {
            libc::getnameinfo(
                (&socket_address as *const libc::sockaddr_storage).cast::<libc::sockaddr>(),
                socket_address_len,
                host.as_mut_ptr().cast(),
                host.len() as libc::socklen_t,
                ptr::null_mut(),
                0,
                libc::NI_NAMEREQD,
            )
        };
        let system_code = if code == libc::EAI_SYSTEM {
            system_error_code()
        } else {
            0
        };
        (code, system_code)
    };
    if code != 0 {
        return Err(classify_resolver_error(code, system_code));
    }

    let name = unsafe { CStr::from_ptr(host.as_ptr().cast()) }
        .to_bytes()
        .to_vec();
    if name.is_empty() {
        return Err(ResolveFailure::new(RESOLVE_UNEXPECTED, 0, 0));
    }
    Ok(vec![name])
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__net_lookup_host(
    host: RtString,
    len_out: *mut usize,
    kind_out: *mut u8,
    resolver_code_out: *mut i32,
    system_code_out: *mut i32,
) -> usize {
    if !prepare_outputs(len_out, kind_out, resolver_code_out, system_code_out) {
        return 0;
    }
    match lookup_host(host) {
        Ok(entries) => {
            unsafe { len_out.write(entries.len()) };
            Box::into_raw(Box::new(ResolverSnapshot::Addresses(entries))) as usize
        }
        Err(failure) => {
            write_failure(failure, kind_out, resolver_code_out, system_code_out);
            0
        }
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__net_lookup_address(
    family: u8,
    address: *const u8,
    len_out: *mut usize,
    kind_out: *mut u8,
    resolver_code_out: *mut i32,
    system_code_out: *mut i32,
) -> usize {
    if !prepare_outputs(len_out, kind_out, resolver_code_out, system_code_out) {
        return 0;
    }
    match lookup_address(family, address) {
        Ok(names) => {
            unsafe { len_out.write(names.len()) };
            Box::into_raw(Box::new(ResolverSnapshot::Names(names))) as usize
        }
        Err(failure) => {
            write_failure(failure, kind_out, resolver_code_out, system_code_out);
            0
        }
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__net_ip_snapshot_at(
    handle: usize,
    index: usize,
    family_out: *mut u8,
    address_out: *mut u8,
) -> i32 {
    if handle == 0 || family_out.is_null() || address_out.is_null() {
        return libc::EINVAL;
    }
    let snapshot = unsafe { &*(handle as *const ResolverSnapshot) };
    let ResolverSnapshot::Addresses(entries) = snapshot else {
        return libc::EINVAL;
    };
    let Some(entry) = entries.get(index) else {
        return libc::EINVAL;
    };
    unsafe {
        family_out.write(entry.family);
        ptr::copy_nonoverlapping(entry.octets.as_ptr(), address_out, entry.octets.len());
    }
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__net_name_snapshot_at(
    handle: usize,
    index: usize,
    data_out: *mut *const u8,
    len_out: *mut usize,
) -> i32 {
    if handle == 0 || data_out.is_null() || len_out.is_null() {
        return libc::EINVAL;
    }
    let snapshot = unsafe { &*(handle as *const ResolverSnapshot) };
    let ResolverSnapshot::Names(names) = snapshot else {
        return libc::EINVAL;
    };
    let Some(name) = names.get(index) else {
        return libc::EINVAL;
    };
    unsafe {
        data_out.write(name.as_ptr());
        len_out.write(name.len());
    }
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__net_snapshot_close(handle: usize) {
    if handle != 0 {
        unsafe { drop(Box::from_raw(handle as *mut ResolverSnapshot)) };
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rt_bytes(bytes: &[u8]) -> RtString {
        RtString {
            ptr: bytes.as_ptr(),
            len: bytes.len(),
        }
    }

    #[test]
    fn numeric_hosts_resolve_to_their_original_family() {
        let ipv4 = lookup_host(rt_bytes(b"127.0.0.1")).expect("IPv4 literal should resolve");
        assert_eq!(ipv4[0].family, ADDRESS_FAMILY_IPV4);
        assert_eq!(&ipv4[0].octets[..4], &[127, 0, 0, 1]);

        let ipv6 = lookup_host(rt_bytes(b"::1")).expect("IPv6 literal should resolve");
        assert_eq!(ipv6[0].family, ADDRESS_FAMILY_IPV6);
        assert_eq!(ipv6[0].octets[15], 1);
    }

    #[test]
    fn invalid_and_empty_hosts_have_stable_kinds() {
        assert_eq!(
            lookup_host(rt_bytes(b"")).unwrap_err().kind,
            RESOLVE_NOT_FOUND
        );
        assert_eq!(
            lookup_host(rt_bytes(b"bad\0host")).unwrap_err().kind,
            RESOLVE_INVALID_INPUT
        );
    }

    #[test]
    fn address_snapshots_retain_multiple_results_in_order() {
        let entries = vec![
            AddressEntry {
                family: ADDRESS_FAMILY_IPV6,
                octets: [1; 16],
            },
            AddressEntry {
                family: ADDRESS_FAMILY_IPV4,
                octets: [2; 16],
            },
        ];
        let handle = Box::into_raw(Box::new(ResolverSnapshot::Addresses(entries))) as usize;
        let mut family = 0;
        let mut octets = [0; 16];
        assert_eq!(
            __rt__net_ip_snapshot_at(handle, 0, &mut family, octets.as_mut_ptr()),
            0
        );
        assert_eq!(family, ADDRESS_FAMILY_IPV6);
        assert_eq!(octets, [1; 16]);
        assert_eq!(
            __rt__net_ip_snapshot_at(handle, 1, &mut family, octets.as_mut_ptr()),
            0
        );
        assert_eq!(family, ADDRESS_FAMILY_IPV4);
        assert_eq!(octets, [2; 16]);
        assert_eq!(
            __rt__net_ip_snapshot_at(handle, 2, &mut family, octets.as_mut_ptr()),
            libc::EINVAL
        );
        __rt__net_snapshot_close(handle);
    }

    #[test]
    fn reverse_lookup_rejects_unknown_address_families() {
        let address = [0_u8; 16];
        let error = lookup_address(99, address.as_ptr()).unwrap_err();
        assert_eq!(error.kind, RESOLVE_UNSUPPORTED);
    }
}
