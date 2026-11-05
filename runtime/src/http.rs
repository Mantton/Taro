//! Bounded HTTP/1 syntax and URL parsing. httparse/http own grammar; std
//! owns streaming, framing, pooling and reactor I/O. Snapshots never retain GC
//! pointers and must be copied/closed synchronously by the std wrappers.
use crate::panic_unwind::RtString;
use http::{HeaderName, HeaderValue, Method};
use std::cell::Cell;
#[derive(Default, Debug)]
struct Snapshot {
    // 0 = success, 1 = incomplete head, 2 = protocol, 3 = transport,
    // 4 = configured limit, 5 = closed client, 6 = timeout, 7 = invalid API input.
    code: usize,
    status: usize,
    consumed: usize,
    length: usize,
    chunked: bool,
    close: bool,
    eof: bool,
    error: Vec<u8>,
    method: SnapshotBytes,
    target: SnapshotBytes,
    authority: Vec<u8>,
    headers: Vec<(SnapshotBytes, SnapshotBytes)>,
}
/// Text the parser usually needn't copy. `Input` points into the buffer being
/// parsed: std's wrappers copy a snapshot out and close it, without suspending,
/// while that buffer stays alive and unchanged.
#[derive(Debug)]
enum SnapshotBytes {
    Static(&'static [u8]),
    Input(*const u8, usize),
    Owned(Vec<u8>),
}
impl Default for SnapshotBytes {
    fn default() -> Self {
        Self::Static(&[])
    }
}
impl SnapshotBytes {
    fn input(bytes: &[u8]) -> Self {
        Self::Input(bytes.as_ptr(), bytes.len())
    }
    fn as_slice(&self) -> &[u8] {
        match self {
            Self::Static(bytes) => bytes,
            Self::Input(pointer, length) => unsafe { bytes(*pointer, *length) },
            Self::Owned(bytes) => bytes,
        }
    }
}
/// How many headers fit in the parser's stack storage. Requests with more use
/// the heap, up to the configured limit.
const INLINE_HEADERS: usize = 32;
/// `__rt__http_snapshot_info` field `SNAPSHOT_TEXT_IS_STATIC + n` reports whether
/// `__rt__http_snapshot_bytes` field `n` is process-long, so std needn't copy it.
const SNAPSHOT_TEXT_IS_STATIC: usize = 1 << 32;
impl Snapshot {
    fn text(&self, field: usize) -> Option<&SnapshotBytes> {
        match field {
            1 => Some(&self.method),
            2 => Some(&self.target),
            0 | 3 => None,
            n => self
                .headers
                .get((n - 4) / 2)
                .map(|(name, content)| if n % 2 == 0 { name } else { content }),
        }
    }
    fn failure(code: usize, message: impl ToString) -> Self {
        Self {
            code,
            error: message.to_string().into_bytes(),
            ..Self::default()
        }
    }
    fn boxed(self) -> usize {
        let snapshot = match SPARE_SNAPSHOT.with(Cell::take) {
            Some(mut spare) => {
                *spare = self;
                spare
            }
            None => Box::new(self),
        };
        Box::into_raw(snapshot) as usize
    }
}
// A snapshot lasts only from parsing until std has copied it out, without
// suspending, so each thread needs one. Keeping it spares two allocations for
// every parse.
thread_local! {
    static SPARE_SNAPSHOT: Cell<Option<Box<Snapshot>>> = const { Cell::new(None) };
}
const SPARE_HEADER_CAPACITY: usize = 64;
fn spare_headers() -> Vec<(SnapshotBytes, SnapshotBytes)> {
    SPARE_SNAPSHOT.with(|slot| {
        let mut spare = slot.take();
        let headers = spare
            .as_mut()
            .map_or_else(Vec::new, |spare| std::mem::take(&mut spare.headers));
        slot.set(spare);
        headers
    })
}
/// Whether every CR and LF is part of a CRLF. Most of a head is neither.
fn line_endings_are_crlf(input: &[u8]) -> bool {
    const LOW: u64 = 0x0101_0101_0101_0101;
    const HIGH: u64 = 0x8080_8080_8080_8080;
    let has = |word: u64, byte: u8| {
        let different = word ^ (LOW * u64::from(byte));
        different.wrapping_sub(LOW) & !different & HIGH != 0
    };
    let mut index = 0;
    while index < input.len() {
        if let Some(chunk) = input.get(index..index + 8) {
            let word = u64::from_ne_bytes(chunk.try_into().expect("eight bytes"));
            if !has(word, b'\r') && !has(word, b'\n') {
                index += 8;
                continue;
            }
        }
        match input[index] {
            b'\r' if input.get(index + 1) == Some(&b'\n') => index += 2,
            b'\r' | b'\n' => return false,
            _ => index += 1,
        }
    }
    true
}
unsafe fn bytes<'a>(ptr: *const u8, len: usize) -> &'a [u8] {
    if len == 0 {
        &[]
    } else {
        unsafe { std::slice::from_raw_parts(ptr, len) }
    }
}
/// `HeaderValue::from_bytes` accepts exactly these bytes, but copies them into a
/// new allocation only for us to throw it away.
const MAX_HEADER_NAME_BYTES: usize = (1 << 16) - 1;
/// Whether `HeaderName::from_bytes` would accept this, without normalizing it.
fn header_name_valid(name: &[u8]) -> bool {
    static TOKEN: [bool; 256] = {
        let mut table = [false; 256];
        let mut byte = 0;
        while byte < 256 {
            table[byte] = (byte as u8).is_ascii_alphanumeric();
            byte += 1;
        }
        let punctuation = b"!#$%&'*+-.^_`|~";
        let mut index = 0;
        while index < punctuation.len() {
            table[punctuation[index] as usize] = true;
            index += 1;
        }
        table
    };
    !name.is_empty()
        && name.len() <= MAX_HEADER_NAME_BYTES
        && name
            .iter()
            .fold(true, |valid, &byte| valid & TOKEN[byte as usize])
}
fn header_value_valid(value: &[u8]) -> bool {
    // Not stopping early lets this compile to vector code, and values are valid.
    value.iter().fold(true, |valid, &byte| {
        valid & (((byte >= 32) & (byte != 127)) | (byte == b'\t'))
    })
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __rt__http_header_valid(name: RtString, value: RtString) -> bool {
    if (name.ptr.is_null() && name.len != 0) || (value.ptr.is_null() && value.len != 0) {
        return false;
    }
    header_name_valid(unsafe { bytes(name.ptr, name.len) })
        && header_value_valid(unsafe { bytes(value.ptr, value.len) })
}

fn common_request_header(name: &str) -> Option<&'static [u8]> {
    Some(match name {
        "host" => b"host",
        "user-agent" => b"user-agent",
        "accept" => b"accept",
        "accept-encoding" => b"accept-encoding",
        "accept-language" => b"accept-language",
        "connection" => b"connection",
        "content-type" => b"content-type",
        "content-length" => b"content-length",
        "cookie" => b"cookie",
        "authorization" => b"authorization",
        _ => return None,
    })
}

fn common_method(method: &str) -> Option<&'static [u8]> {
    Some(match method {
        "GET" => b"GET",
        "POST" => b"POST",
        "PUT" => b"PUT",
        "DELETE" => b"DELETE",
        "HEAD" => b"HEAD",
        "OPTIONS" => b"OPTIONS",
        "PATCH" => b"PATCH",
        _ => return None,
    })
}
/// A dotted name or IPv4 address with an optional numeric port, which is nearly
/// every Host. It lets the check skip the copy that parsing an Authority makes.
fn plain_authority(raw: &[u8]) -> bool {
    if !raw.first().is_some_and(u8::is_ascii_alphanumeric) {
        return false;
    }
    let mut index = 1;
    while index < raw.len() {
        let byte = raw[index];
        if byte == b':' {
            let port = &raw[index + 1..];
            return !port.is_empty() && port.iter().all(u8::is_ascii_digit);
        }
        if !(byte.is_ascii_alphanumeric() || byte == b'.' || byte == b'-') {
            return false;
        }
        index += 1;
    }
    true
}
fn general_authority(raw: &[u8]) -> bool {
    let authority = std::str::from_utf8(raw)
        .ok()
        .and_then(|s| s.parse::<http::uri::Authority>().ok());
    raw.is_ascii()
        && !raw.contains(&b'@')
        && authority.is_some()
        && !raw.iter().any(u8::is_ascii_whitespace)
}
/// Validate a request head. Its `headers` are only kept when asked for: a request's
/// are normally read later, if at all, by parsing the same bytes again.
fn parse_head(
    input: &[u8],
    max_headers: usize,
    max_body: usize,
    keep_headers: bool,
) -> Result<Snapshot, Snapshot> {
    let limit = max_headers.min(1024);
    let mut inline =
        [const { std::mem::MaybeUninit::<httparse::Header<'_>>::uninit() }; INLINE_HEADERS];
    let mut spilled = Vec::new();
    let mut request = httparse::Request::new(&mut []);
    let mut parsed =
        request.parse_with_uninit_headers(input, &mut inline[..limit.min(INLINE_HEADERS)]);
    if parsed == Err(httparse::Error::TooManyHeaders) && limit > INLINE_HEADERS {
        // Only now are the configured limit's worth of slots worth allocating.
        spilled.resize_with(limit, std::mem::MaybeUninit::uninit);
        request = httparse::Request::new(&mut []);
        parsed = request.parse_with_uninit_headers(input, &mut spilled[..]);
    }
    let consumed = match parsed.map_err(|e| {
        Snapshot::failure(
            if e == httparse::Error::TooManyHeaders {
                4
            } else {
                2
            },
            e,
        )
    })? {
        httparse::Status::Partial => return Err(Snapshot::failure(1, "incomplete HTTP head")),
        httparse::Status::Complete(n) => n,
    };
    // httparse accepts LF for interoperability. Our server deliberately requires
    // CRLF and rejects ambiguous framing before running application handlers.
    if !line_endings_are_crlf(&input[..consumed]) {
        return Err(Snapshot::failure(2, "HTTP requires CRLF"));
    }
    if request.version != Some(1) {
        return Err(Snapshot::failure(2, "server requires HTTP/1.1"));
    }
    let method = request.method.unwrap_or_default();
    let target = request.path.unwrap_or_default();
    if target.bytes().any(|b| !(0x21..=0x7e).contains(&b)) || target.contains('#') {
        return Err(Snapshot::failure(2, "invalid HTTP request target"));
    }
    if method == "CONNECT" || !(target.starts_with('/') || (method == "OPTIONS" && target == "*")) {
        return Err(Snapshot::failure(
            2,
            "server requires origin-form request target",
        ));
    }
    let mut result = Snapshot {
        consumed,
        method: common_method(method).map_or_else(
            || SnapshotBytes::input(method.as_bytes()),
            SnapshotBytes::Static,
        ),
        target: SnapshotBytes::input(target.as_bytes()),
        ..Snapshot::default()
    };
    if keep_headers {
        result.headers = spare_headers();
        result.headers.reserve(request.headers.len());
    }
    let mut host = false;
    let mut length = None;
    let mut transfer = false;
    for header in request.headers.iter() {
        if !header_name_valid(header.name.as_bytes()) {
            return Err(Snapshot::failure(2, "invalid header name"));
        }
        let raw = header.value;
        if !header_value_valid(raw) {
            return Err(Snapshot::failure(2, "invalid header value"));
        }
        // Valid names are ASCII, and few are long.
        let mut stack = [0u8; 64];
        let long;
        let name = if let Some(lowered) = stack.get_mut(..header.name.len()) {
            lowered.copy_from_slice(header.name.as_bytes());
            lowered.make_ascii_lowercase();
            // SAFETY: it's a valid name, which is ASCII.
            unsafe { std::str::from_utf8_unchecked(lowered) }
        } else {
            long = header.name.to_ascii_lowercase();
            long.as_str()
        };
        match name {
            "host" => {
                if host || raw.is_empty() || raw.contains(&b',') {
                    return Err(Snapshot::failure(2, "one Host header required"));
                }
                if !plain_authority(raw) && !general_authority(raw) {
                    return Err(Snapshot::failure(2, "invalid Host authority"));
                }
                host = true;
            }
            "content-length" => {
                if length.is_some() || raw.is_empty() || !raw.iter().all(u8::is_ascii_digit) {
                    return Err(Snapshot::failure(2, "ambiguous Content-Length"));
                }
                let value: usize = std::str::from_utf8(raw)
                    .unwrap()
                    .parse()
                    .map_err(|_| Snapshot::failure(4, "Content-Length overflow"))?;
                if value > max_body {
                    return Err(Snapshot::failure(
                        4,
                        "HTTP request body exceeds configured limit",
                    ));
                }
                length = Some(value);
            }
            "transfer-encoding" => {
                if transfer || !raw.eq_ignore_ascii_case(b"chunked") {
                    return Err(Snapshot::failure(2, "unsupported Transfer-Encoding"));
                }
                transfer = true;
            }
            "expect" | "upgrade" => {
                return Err(Snapshot::failure(
                    2,
                    "Expect and protocol upgrades are unsupported",
                ));
            }
            "connection" => {
                result.close |= raw
                    .split(|byte| *byte == b',')
                    .any(|token| token.trim_ascii().eq_ignore_ascii_case(b"close"));
            }
            _ => {}
        }
        if !keep_headers {
            continue;
        }
        // Common names are static, and the wire spelling serves when already
        // lowercase. Only an unusual name in another case needs a copy.
        let lowered = if let Some(common) = common_request_header(name) {
            SnapshotBytes::Static(common)
        } else if header.name == name {
            SnapshotBytes::input(header.name.as_bytes())
        } else {
            SnapshotBytes::Owned(name.as_bytes().to_vec())
        };
        result.headers.push((lowered, SnapshotBytes::input(raw)));
    }
    if !host || (transfer && length.is_some()) {
        return Err(Snapshot::failure(
            2,
            "missing Host or ambiguous request framing",
        ));
    }
    result.length = length.unwrap_or(0);
    result.chunked = transfer;
    Ok(result)
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __rt__http_parse_head(
    ptr: *const u8,
    len: usize,
    max_headers: usize,
    max_body: usize,
) -> usize {
    parse_head(unsafe { bytes(ptr, len) }, max_headers, max_body, true)
        .unwrap_or_else(|e| e)
        .boxed()
}

/// What std needs from a valid request head, as std's `CheckedHead` declares it.
/// A request's headers are read later, if at all, by parsing the same bytes again.
#[repr(C)]
pub struct CheckedHead {
    /// Process-long when `method_is_static`, otherwise within the input.
    method: *const u8,
    method_len: usize,
    method_is_static: usize,
    /// Within the input.
    target: *const u8,
    target_len: usize,
    consumed: usize,
    length: usize,
    chunked: usize,
    close: usize,
}

/// Fill `out` from a valid head and return 0, or return a snapshot of its failure.
///
/// # Safety
/// `ptr` and `len` are readable bytes, and `out` is writable.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __rt__http_check_head(
    ptr: *const u8,
    len: usize,
    max_headers: usize,
    max_body: usize,
    out: *mut CheckedHead,
) -> usize {
    let parsed = match parse_head(unsafe { bytes(ptr, len) }, max_headers, max_body, false) {
        Ok(parsed) => parsed,
        Err(failure) => return failure.boxed(),
    };
    // Only normalized text would be neither, and requests have none.
    let SnapshotBytes::Input(target, target_len) = parsed.target else {
        return Snapshot::failure(2, "request target was normalized").boxed();
    };
    let (method, method_len, method_is_static) = match parsed.method {
        SnapshotBytes::Static(text) => (text.as_ptr(), text.len(), 1),
        SnapshotBytes::Input(method, method_len) => (method, method_len, 0),
        SnapshotBytes::Owned(_) => {
            return Snapshot::failure(2, "request method was normalized").boxed();
        }
    };
    unsafe {
        out.write(CheckedHead {
            method,
            method_len,
            method_is_static,
            target,
            target_len,
            consumed: parsed.consumed,
            length: parsed.length,
            chunked: usize::from(parsed.chunked),
            close: usize::from(parsed.close),
        });
    }
    0
}

fn parse_response(
    input: &[u8],
    max_headers: usize,
    max_body: usize,
    head: bool,
) -> Result<Snapshot, Snapshot> {
    let mut headers = vec![httparse::EMPTY_HEADER; max_headers.min(1024)];
    let mut response = httparse::Response::new(&mut headers);
    let consumed = match response.parse(input).map_err(|e| {
        Snapshot::failure(
            if e == httparse::Error::TooManyHeaders {
                4
            } else {
                2
            },
            e,
        )
    })? {
        httparse::Status::Partial => return Err(Snapshot::failure(1, "incomplete HTTP head")),
        httparse::Status::Complete(n) => n,
    };
    if input[..consumed].iter().enumerate().any(|(i, b)| {
        (*b == b'\n' && (i == 0 || input[i - 1] != b'\r'))
            || (*b == b'\r' && input.get(i + 1) != Some(&b'\n'))
    }) {
        return Err(Snapshot::failure(2, "HTTP requires CRLF"));
    }
    let status = response.code.unwrap_or(0) as usize;
    if status < 100 || status == 101 || status > 599 {
        return Err(Snapshot::failure(2, "unsupported HTTP status/upgrade"));
    }
    let mut result = Snapshot {
        consumed,
        status,
        close: response.version != Some(1),
        ..Snapshot::default()
    };
    let mut length = None;
    let mut transfer = false;
    for header in response.headers.iter() {
        let name = HeaderName::from_bytes(header.name.as_bytes())
            .map_err(|_| Snapshot::failure(2, "invalid response header"))?;
        let value = HeaderValue::from_bytes(header.value)
            .map_err(|_| Snapshot::failure(2, "invalid response header value"))?;
        let raw = value.as_bytes();
        match name.as_str() {
            "content-length" => {
                if length.is_some() || raw.is_empty() || !raw.iter().all(u8::is_ascii_digit) {
                    return Err(Snapshot::failure(2, "ambiguous Content-Length"));
                }
                length = Some(
                    std::str::from_utf8(raw)
                        .unwrap()
                        .parse::<usize>()
                        .map_err(|_| Snapshot::failure(4, "Content-Length overflow"))?,
                );
            }
            "transfer-encoding" => {
                if transfer || !raw.eq_ignore_ascii_case(b"chunked") {
                    return Err(Snapshot::failure(2, "unsupported Transfer-Encoding"));
                }
                transfer = true;
            }
            "connection" => {
                if raw
                    .split(|b| *b == b',')
                    .any(|token| token.trim_ascii().eq_ignore_ascii_case(b"close"))
                {
                    result.close = true;
                }
            }
            "upgrade" => return Err(Snapshot::failure(2, "protocol upgrades unsupported")),
            _ => {}
        }
        result.headers.push((
            SnapshotBytes::Owned(name.as_str().as_bytes().to_vec()),
            SnapshotBytes::Owned(raw.to_vec()),
        ));
    }
    if transfer && length.is_some() {
        return Err(Snapshot::failure(2, "ambiguous HTTP framing"));
    }
    if status == 205 && length.is_some_and(|n| n != 0) {
        return Err(Snapshot::failure(2, "205 response forbids content"));
    }
    let empty = head || status < 200 || status == 204 || status == 304;
    if status == 204 && (transfer || length.is_some()) {
        return Err(Snapshot::failure(2, "204 response cannot carry framing"));
    }
    if status < 200 && (transfer || length.is_some()) {
        return Err(Snapshot::failure(
            2,
            "informational response cannot carry framing",
        ));
    }
    result.length = if empty { 0 } else { length.unwrap_or(0) };
    if result.length > max_body {
        return Err(Snapshot::failure(4, "HTTP body exceeds configured limit"));
    }
    result.chunked = !empty && transfer;
    result.eof = !empty && !transfer && length.is_none();
    result.close |= result.eof;
    Ok(result)
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __rt__http_parse_response(
    ptr: *const u8,
    len: usize,
    max_headers: usize,
    max_body: usize,
    head: bool,
) -> usize {
    parse_response(unsafe { bytes(ptr, len) }, max_headers, max_body, head)
        .unwrap_or_else(|e| e)
        .boxed()
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __rt__http_url(url: RtString, method: RtString) -> usize {
    let parse = || -> Result<Snapshot, Snapshot> {
        let url = std::str::from_utf8(unsafe { bytes(url.ptr, url.len) })
            .map_err(|_| Snapshot::failure(7, "invalid URL"))?;
        let method = Method::from_bytes(unsafe { bytes(method.ptr, method.len) })
            .map_err(|_| Snapshot::failure(7, "invalid HTTP method"))?;
        if method == Method::CONNECT || url.contains('#') {
            return Err(Snapshot::failure(7, "unsupported HTTP target"));
        }
        let uri: http::Uri = url
            .parse()
            .map_err(|_| Snapshot::failure(7, "invalid absolute URL"))?;
        let secure = match uri.scheme_str() {
            Some("http") => false,
            Some("https") => true,
            _ => return Err(Snapshot::failure(7, "expected http:// or https:// URL")),
        };
        let authority = uri
            .authority()
            .ok_or_else(|| Snapshot::failure(7, "URL authority required"))?;
        if authority.as_str().contains('@') {
            return Err(Snapshot::failure(7, "URL credentials unsupported"));
        }
        if authority.as_str().len() > authority.host().len() && authority.port_u16().is_none() {
            return Err(Snapshot::failure(7, "invalid URL port"));
        }
        let host = authority
            .host()
            .trim_start_matches('[')
            .trim_end_matches(']');
        if host.is_empty() {
            return Err(Snapshot::failure(7, "URL host required"));
        }
        let path = uri.path_and_query().map_or("/", |p| p.as_str());
        let target = if path.starts_with('?') {
            format!("/{path}").into_bytes()
        } else {
            path.as_bytes().to_vec()
        };
        Ok(Snapshot {
            method: SnapshotBytes::Owned(host.as_bytes().to_vec()),
            target: SnapshotBytes::Owned(target),
            authority: authority.as_str().as_bytes().to_vec(),
            length: authority
                .port_u16()
                .map_or(if secure { 443 } else { 80 }, usize::from),
            chunked: secure,
            ..Snapshot::default()
        })
    };
    parse().unwrap_or_else(|e| e).boxed()
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __rt__http_chunk_size(line: RtString, out: *mut usize) -> bool {
    let input = unsafe { bytes(line.ptr, line.len) };
    match httparse::parse_chunk_size(input) {
        Ok(httparse::Status::Complete((n, value)))
            if n == input.len() && usize::try_from(value).is_ok() && input.ends_with(b"\r\n") =>
        {
            unsafe { out.write(value as usize) };
            true
        }
        _ => false,
    }
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __rt__http_snapshot_info(handle: usize, field: usize) -> usize {
    let value = unsafe { &*(handle as *const Snapshot) };
    match field {
        0 => value.code,
        1 => value.status,
        2 => value.headers.len(),
        3 => value.consumed,
        4 => value.length,
        5 => usize::from(value.chunked),
        6 => usize::from(value.close),
        7 => usize::from(value.eof),
        field if field >= SNAPSHOT_TEXT_IS_STATIC => usize::from(
            value
                .text(field - SNAPSHOT_TEXT_IS_STATIC)
                .is_some_and(|text| matches!(text, SnapshotBytes::Static(_))),
        ),
        _ => 0,
    }
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __rt__http_snapshot_bytes(
    handle: usize,
    field: usize,
    len: *mut usize,
) -> *const u8 {
    let value = unsafe { &*(handle as *const Snapshot) };
    let data: &[u8] = match field {
        0 => &value.error,
        1 => value.method.as_slice(),
        2 => value.target.as_slice(),
        3 => &value.authority,
        n => value
            .headers
            .get((n - 4) / 2)
            .map(|(name, content)| {
                if n % 2 == 0 {
                    name.as_slice()
                } else {
                    content.as_slice()
                }
            })
            .unwrap_or(&[]),
    };
    unsafe { len.write(data.len()) };
    data.as_ptr()
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __rt__http_snapshot_close(handle: usize) {
    if handle != 0 {
        let mut snapshot = unsafe { Box::from_raw(handle as *mut Snapshot) };
        // What's left is never read, and goes when the next parse replaces it.
        snapshot.headers.clear();
        if snapshot.headers.capacity() > SPARE_HEADER_CAPACITY {
            snapshot.headers = Vec::new();
        }
        // Only a thread already exiting can fail this, and then the box just drops.
        let _ = SPARE_SNAPSHOT.try_with(|slot| slot.set(Some(snapshot)));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn parsed_header_names(head: &[u8]) -> Vec<Vec<u8>> {
        let handle = unsafe { __rt__http_parse_head(head.as_ptr(), head.len(), 64, 1024) };
        let snapshot = unsafe { &*(handle as *const Snapshot) };
        assert_eq!(snapshot.code, 0);
        let names = snapshot
            .headers
            .iter()
            .map(|(name, _)| name.as_slice().to_vec())
            .collect();
        unsafe { __rt__http_snapshot_close(handle) };
        names
    }

    #[test]
    fn a_reused_snapshot_holds_only_the_latest_parse() {
        let long = b"GET / HTTP/1.1\r\nhost: a\r\nx-one: 1\r\nX-Upper: 2\r\n\r\n";
        assert_eq!(parsed_header_names(long).len(), 3);
        let short = b"GET /other HTTP/1.1\r\nhost: b\r\n\r\n";
        assert_eq!(parsed_header_names(short), vec![b"host".to_vec()]);
        // A failure reuses the same storage, and must not report earlier fields.
        let bad = b"GET bad HTTP/1.1\r\nhost: b\r\n\r\n";
        let handle = unsafe { __rt__http_parse_head(bad.as_ptr(), bad.len(), 64, 1024) };
        let snapshot = unsafe { &*(handle as *const Snapshot) };
        assert_eq!(snapshot.code, 2);
        assert!(snapshot.headers.is_empty());
        unsafe { __rt__http_snapshot_close(handle) };
        assert_eq!(parsed_header_names(long).len(), 3);
    }

    #[test]
    fn an_unusually_large_snapshot_is_not_kept() {
        let mut head = b"GET / HTTP/1.1\r\nhost: a\r\n".to_vec();
        for index in 0..SPARE_HEADER_CAPACITY + 8 {
            head.extend_from_slice(format!("x-{index}: 1\r\n").as_bytes());
        }
        head.extend_from_slice(b"\r\n");
        let handle = unsafe { __rt__http_parse_head(head.as_ptr(), head.len(), 1024, 1024) };
        unsafe { __rt__http_snapshot_close(handle) };
        assert_eq!(spare_headers().capacity(), 0);
    }

    #[test]
    fn absolute_urls_normalize_empty_paths_and_validate_ports() {
        fn parse(url: &str) -> Box<Snapshot> {
            let url = RtString {
                ptr: url.as_ptr(),
                len: url.len(),
            };
            let method = RtString {
                ptr: b"GET".as_ptr(),
                len: 3,
            };
            unsafe { Box::from_raw(__rt__http_url(url, method) as *mut Snapshot) }
        }
        assert_eq!(parse("http://localhost?x=1").target.as_slice(), b"/?x=1");
        assert_eq!(parse("https://[::1]:8443/").method.as_slice(), b"::1");
        assert_eq!(parse("https://localhost:8443/").length, 8443);
        for url in [
            "http://x:99999/",
            "http://x:/",
            "http://a@b/",
            "http://x/#fragment",
            "file:///tmp/x",
        ] {
            assert_eq!(parse(url).code, 7, "invalid URL: {url}");
        }
    }

    #[test]
    fn line_ending_check_accepts_exactly_paired_crlf() {
        fn naive(input: &[u8]) -> bool {
            !input.iter().enumerate().any(|(i, b)| {
                (*b == b'\n' && (i == 0 || input[i - 1] != b'\r'))
                    || (*b == b'\r' && input.get(i + 1) != Some(&b'\n'))
            })
        }
        // Every string of these up to length 7, then each placed around a word edge.
        const ALPHABET: [u8; 3] = [b'\r', b'\n', b'a'];
        for len in 0..=7u32 {
            for mut code in 0..3usize.pow(len) {
                let mut input = Vec::new();
                for _ in 0..len {
                    input.push(ALPHABET[code % 3]);
                    code /= 3;
                }
                assert_eq!(line_endings_are_crlf(&input), naive(&input), "{input:?}");
                for padding in [5, 7, 8, 9, 15, 16, 17] {
                    let mut padded = vec![b'x'; padding];
                    padded.extend_from_slice(&input);
                    padded.extend_from_slice(&[b'y'; 11]);
                    assert_eq!(line_endings_are_crlf(&padded), naive(&padded), "{padded:?}");
                }
            }
        }
    }

    #[test]
    fn parsed_header_names_are_lowered_like_the_http_crate() {
        let name_of = |name: &str| {
            let head = format!("GET / HTTP/1.1\r\nHost: a\r\n{name}: v\r\n\r\n");
            let parsed = parse_head(head.as_bytes(), 8, 8, true).ok().unwrap();
            parsed.headers[1].0.as_slice().to_vec()
        };
        for name in [
            "x-mixed",
            "X-Mixed",
            "ACCEPT",
            "Accept",
            &"Long-Name-".repeat(9),
        ] {
            assert_eq!(
                name_of(name),
                HeaderName::from_bytes(name.as_bytes())
                    .unwrap()
                    .as_str()
                    .as_bytes(),
            );
        }
    }

    #[test]
    fn header_name_validation_matches_the_http_crate() {
        for byte in 0..=u8::MAX {
            for name in [[byte].as_slice(), &[b'a', byte, b'z']] {
                assert_eq!(
                    header_name_valid(name),
                    HeaderName::from_bytes(name).is_ok(),
                    "byte {byte}"
                );
            }
        }
        assert_eq!(header_name_valid(b""), HeaderName::from_bytes(b"").is_ok());
        for len in [64, 65, MAX_HEADER_NAME_BYTES, MAX_HEADER_NAME_BYTES + 1] {
            let name = vec![b'a'; len];
            assert_eq!(
                header_name_valid(&name),
                HeaderName::from_bytes(&name).is_ok(),
                "{len} bytes"
            );
        }
    }

    #[test]
    fn a_request_asks_to_close_with_any_connection_token() {
        let closes = |value: &str| {
            let head = format!("GET / HTTP/1.1\r\nHost: a\r\nConnection: {value}\r\n\r\n");
            parse_head(head.as_bytes(), 8, 8, true).ok().unwrap().close
        };
        assert!(closes("close"));
        assert!(closes("CLOSE"));
        assert!(closes("keep-alive, close"));
        assert!(closes("upgrade,\tClose ,x"));
        assert!(!closes("keep-alive"));
        assert!(!closes("closed"));
        assert!(!closes("not close"));
    }

    #[test]
    fn header_value_validation_matches_the_http_crate_for_every_byte() {
        for byte in 0..=u8::MAX {
            let value = [b'a', byte, b'z'];
            assert_eq!(
                header_value_valid(&value),
                HeaderValue::from_bytes(&value).is_ok(),
                "byte {byte}"
            );
        }
    }

    #[test]
    fn every_plain_authority_is_a_valid_general_one() {
        // A plain authority skips the general check, so it can't accept more.
        let hosts = [
            "a",
            "a.b",
            "a-b",
            "1",
            "127.0.0.1",
            "a.",
            "a..b",
            "a-",
            "EXAMPLE.com",
        ];
        let ports = ["", ":0", ":80", ":65535", ":65536", ":99999999"];
        for host in hosts {
            for port in ports {
                let authority = format!("{host}{port}");
                assert!(plain_authority(authority.as_bytes()), "{authority}");
                assert!(general_authority(authority.as_bytes()), "{authority}");
            }
        }
        for authority in [
            "", ":", ":80", "a:", "a:b", "a:1:2", "-a", ".a", "a b", "a@b", "[::1]", "[::1]:80",
            "a/b", "a?b", "a#b", "a%20", "é",
        ] {
            assert!(!plain_authority(authority.as_bytes()), "{authority}");
        }
        assert!(general_authority(b"[::1]:80"));
    }

    #[test]
    fn host_validation_still_rejects_what_it_rejected() {
        for host in ["a@b", "a b", "a,b", "", "a/b", "[::1"] {
            let input = format!("GET / HTTP/1.1\r\nHost: {host}\r\n\r\n");
            assert_eq!(
                parse_head(input.as_bytes(), 8, 3, true).unwrap_err().code,
                2,
                "{host}"
            );
        }
        // The general parser leaves port digits to whoever reads the port.
        for host in [
            "a",
            "a:80",
            "a:b",
            "127.0.0.1:8080",
            "[::1]:80",
            "EXAMPLE.com",
        ] {
            let input = format!("GET / HTTP/1.1\r\nHost: {host}\r\n\r\n");
            assert!(parse_head(input.as_bytes(), 8, 3, true).is_ok(), "{host}");
        }
    }

    #[test]
    fn only_process_long_text_is_reported_static() {
        let input = b"GET /path HTTP/1.1\r\nHost: x\r\nx-other: y\r\n\r\n";
        let snapshot = Box::into_raw(Box::new(parse_head(input, 8, 3, true).unwrap())) as usize;
        let is_static = |field| unsafe {
            __rt__http_snapshot_info(snapshot, SNAPSHOT_TEXT_IS_STATIC + field) != 0
        };
        // Error, method, target, authority, then name/value for each header.
        let expected = [false, true, false, false, true, false, false, false, false];
        for (field, expected) in expected.into_iter().enumerate() {
            assert_eq!(is_static(field), expected, "field {field}");
        }
        unsafe { __rt__http_snapshot_close(snapshot) };
        let unusual = b"BREW / HTTP/1.1\r\nHost: x\r\n\r\n";
        assert!(matches!(
            parse_head(unusual, 8, 3, true).unwrap().method,
            SnapshotBytes::Input(..)
        ));
    }

    #[test]
    fn parsed_request_text_matches_the_wire_after_normalizing_names() {
        let input = b"GET /path?q=1 HTTP/1.1\r\nHOST: x:1\r\nx-lower: a\r\nX-Mixed: b\r\n\r\n";
        let parsed = parse_head(input, 10, 3, true).unwrap();
        assert_eq!(parsed.method.as_slice(), b"GET");
        assert_eq!(parsed.target.as_slice(), b"/path?q=1");
        let headers: Vec<(&[u8], &[u8])> = parsed
            .headers
            .iter()
            .map(|(name, value)| (name.as_slice(), value.as_slice()))
            .collect();
        assert_eq!(
            headers,
            [
                (&b"host"[..], &b"x:1"[..]),
                (&b"x-lower"[..], &b"a"[..]),
                (&b"x-mixed"[..], &b"b"[..])
            ]
        );
    }

    #[test]
    fn more_headers_than_fit_inline_still_parse_up_to_the_limit() {
        let mut input = b"GET / HTTP/1.1\r\nHost: x\r\n".to_vec();
        for index in 0..INLINE_HEADERS * 2 {
            input.extend_from_slice(format!("x-{index}: v\r\n").as_bytes());
        }
        input.extend_from_slice(b"\r\n");
        let count = INLINE_HEADERS * 2 + 1;
        assert_eq!(
            parse_head(&input, count, 3, true).unwrap().headers.len(),
            count
        );
        assert_eq!(parse_head(&input, count - 1, 3, true).unwrap_err().code, 4);
    }

    #[test]
    fn framing_is_strict_and_bounded() {
        assert_eq!(
            parse_head(
                b"POST / HTTP/1.1\r\nHost: x\r\nContent-Length: 3\r\n\r\n",
                10,
                3,
                true,
            )
            .unwrap()
            .length,
            3
        );
        for bad in [
            &b"GET / HTTP/1.1\nHost: x\n\n"[..],
            &b"GET / HTTP/1.1\r\n\r\n"[..],
            &b"POST / HTTP/1.1\r\nHost: x\r\nContent-Length: 1\r\nContent-Length: 1\r\n\r\n"[..],
            &b"GET / HTTP/1.1\r\nHost: x\r\nHost: y\r\n\r\n"[..],
            &b"POST / HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\nContent-Length: 1\r\n\r\n"[..],
        ] { assert_eq!(parse_head(bad, 10, 3, true).unwrap_err().code, 2); }
        assert!(
            parse_response(
                b"HTTP/1.1 200 OK\r\nContent-Length: 1\r\nTransfer-Encoding: chunked\r\n\r\n",
                10,
                3,
                false
            )
            .is_err()
        );
        assert!(
            parse_response(
                b"HTTP/1.1 200 OK\r\nContent-Length: 4\r\n\r\n",
                10,
                3,
                false
            )
            .is_err()
        );
        assert!(
            parse_response(b"HTTP/1.1 200 OK\r\nContent-Length: 4\r\n\r\n", 10, 3, true).is_ok()
        );
        assert!(
            parse_response(b"HTTP/1.1 200 OK\r\n\r\n", 10, 3, false)
                .unwrap()
                .eof
        );
        assert!(
            !parse_response(
                b"HTTP/1.1 200 OK\r\nContent-Length: 0\r\n\r\n",
                10,
                3,
                false
            )
            .unwrap()
            .eof
        );
    }
}
