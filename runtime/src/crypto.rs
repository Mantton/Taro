//! Standard cryptographic primitives supplied by ring. All input/output slices
//! are borrowed for the synchronous call; only native keys/results are retained.
//! Long operations use the compiler's blocking boundary so GC can proceed.
use ring::{
    aead, digest, hmac,
    rand::{SecureRandom, SystemRandom},
};
use std::{
    collections::HashMap,
    sync::{
        Arc, Mutex, OnceLock,
        atomic::{AtomicU64, Ordering},
    },
};
use subtle::ConstantTimeEq;
use zeroize::{Zeroize, Zeroizing};

const OK: u8 = 0;
const INVALID: u8 = 1;
const ENTROPY: u8 = 2;
const AUTHENTICATION: u8 = 3;
const CLOSED: u8 = 4;
const LIMIT: u8 = 5;
const NONCE_BYTES: usize = 12;
const TAG_BYTES: usize = 16;
const MESSAGE_LIMIT: u64 = 1 << 32;

unsafe fn bytes<'a>(ptr: *const u8, len: usize) -> &'a [u8] {
    if len == 0 {
        &[]
    } else {
        unsafe { std::slice::from_raw_parts(ptr, len) }
    }
}
fn hash_algorithm(algorithm: u8) -> Option<&'static digest::Algorithm> {
    match algorithm {
        0 => Some(&digest::SHA256),
        1 => Some(&digest::SHA512),
        _ => None,
    }
}
fn hmac_algorithm(algorithm: u8) -> Option<hmac::Algorithm> {
    match algorithm {
        0 => Some(hmac::HMAC_SHA256),
        1 => Some(hmac::HMAC_SHA512),
        _ => None,
    }
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __rt__crypto_random(out: *mut u8, len: usize) -> bool {
    if len == 0 {
        return true;
    }
    SystemRandom::new()
        .fill(unsafe { std::slice::from_raw_parts_mut(out, len) })
        .is_ok()
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __rt__crypto_digest(
    algorithm: u8,
    data: *const u8,
    len: usize,
    out: *mut u8,
) -> bool {
    let Some(algorithm) = hash_algorithm(algorithm) else {
        return false;
    };
    let value = digest::digest(algorithm, unsafe { bytes(data, len) });
    unsafe { std::ptr::copy_nonoverlapping(value.as_ref().as_ptr(), out, value.as_ref().len()) };
    true
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __rt__crypto_hmac(
    algorithm: u8,
    key: *const u8,
    key_len: usize,
    data: *const u8,
    len: usize,
    out: *mut u8,
) -> bool {
    let Some(algorithm) = hmac_algorithm(algorithm) else {
        return false;
    };
    let key = hmac::Key::new(algorithm, unsafe { bytes(key, key_len) });
    let tag = hmac::sign(&key, unsafe { bytes(data, len) });
    unsafe { std::ptr::copy_nonoverlapping(tag.as_ref().as_ptr(), out, tag.as_ref().len()) };
    true
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __rt__crypto_hmac_verify(
    algorithm: u8,
    key: *const u8,
    key_len: usize,
    data: *const u8,
    len: usize,
    tag: *const u8,
    tag_len: usize,
) -> bool {
    let Some(algorithm) = hmac_algorithm(algorithm) else {
        return false;
    };
    let key = hmac::Key::new(algorithm, unsafe { bytes(key, key_len) });
    hmac::verify(&key, unsafe { bytes(data, len) }, unsafe {
        bytes(tag, tag_len)
    })
    .is_ok()
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __rt__crypto_equal(
    a: *const u8,
    a_len: usize,
    b: *const u8,
    b_len: usize,
) -> bool {
    // Length is public; content comparison is supplied by subtle, never lowered
    // through the Taro optimizer into an early-exit equality loop.
    a_len == b_len && bool::from(unsafe { bytes(a, a_len) }.ct_eq(unsafe { bytes(b, b_len) }))
}

struct Key {
    cipher: aead::LessSafeKey,
    messages: AtomicU64,
}
#[derive(Default)]
struct Keys {
    next: usize,
    entries: HashMap<usize, Arc<Key>>,
}
fn keys() -> &'static Mutex<Keys> {
    static KEYS: OnceLock<Mutex<Keys>> = OnceLock::new();
    KEYS.get_or_init(Default::default)
}
#[unsafe(no_mangle)]
pub unsafe extern "C-unwind" fn __rt__crypto_aead_new(
    data: *const u8,
    len: usize,
    code: *mut u8,
) -> *mut u8 {
    unsafe { code.write(INVALID) };
    let mut material = Zeroizing::new([0u8; 32]);
    if len == 0 {
        if SystemRandom::new().fill(&mut *material).is_err() {
            unsafe { code.write(ENTROPY) };
            return std::ptr::null_mut();
        }
    } else if len == material.len() {
        material.copy_from_slice(unsafe { bytes(data, len) });
    } else {
        return std::ptr::null_mut();
    }
    let cipher = aead::UnboundKey::new(&aead::AES_256_GCM, &material[..]);
    material.zeroize();
    let Ok(cipher) = cipher else {
        return std::ptr::null_mut();
    };
    let mut table = keys().lock().unwrap_or_else(|p| p.into_inner());
    let Some(next) = table.next.checked_add(1) else {
        unsafe { code.write(LIMIT) };
        return std::ptr::null_mut();
    };
    table.next = next;
    table.entries.insert(
        next,
        Arc::new(Key {
            cipher: aead::LessSafeKey::new(cipher),
            messages: AtomicU64::new(0),
        }),
    );
    unsafe { code.write(OK) };
    drop(table);
    // This owner contains only native bookkeeping. Its reclaimer runs after
    // the world restarts and cannot call Taro or close an OS resource.
    crate::garbage_collector::gc_native_new(next as *mut u8, release_key)
}
fn release_key(id: usize) {
    keys()
        .lock()
        .unwrap_or_else(|p| p.into_inner())
        .entries
        .remove(&id);
}
unsafe fn owner_id(owner: *const u8) -> usize {
    unsafe { owner.cast::<usize>().read() }
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __rt__crypto_aead_close(owner: *const u8) {
    release_key(unsafe { owner_id(owner) });
}
/// Private lifetime oracle used by std's GC regression test.
#[unsafe(no_mangle)]
pub extern "C" fn __rt__crypto_test_live_keys() -> usize {
    keys()
        .lock()
        .unwrap_or_else(|p| p.into_inner())
        .entries
        .len()
}
struct Output {
    code: u8,
    bytes: Vec<u8>,
}
impl Output {
    fn error(code: u8) -> Self {
        Self {
            code,
            bytes: Vec::new(),
        }
    }
}
fn crypt(key: &Key, seal: bool, input: &[u8], aad: &[u8]) -> Output {
    if seal {
        // Reserve a use before drawing randomness. Failed attempts still count.
        if key
            .messages
            .try_update(Ordering::SeqCst, Ordering::SeqCst, |n| {
                (n < MESSAGE_LIMIT).then_some(n + 1)
            })
            .is_err()
        {
            return Output::error(LIMIT);
        }
        let Some(size) = input.len().checked_add(NONCE_BYTES + TAG_BYTES) else {
            return Output::error(LIMIT);
        };
        let mut nonce = [0u8; NONCE_BYTES];
        if SystemRandom::new().fill(&mut nonce).is_err() {
            return Output::error(ENTROPY);
        }
        let mut output = Vec::with_capacity(size);
        output.extend_from_slice(&nonce);
        output.extend_from_slice(input);
        let tag = key.cipher.seal_in_place_separate_tag(
            aead::Nonce::assume_unique_for_key(nonce),
            aead::Aad::from(aad),
            &mut output[NONCE_BYTES..],
        );
        match tag {
            Ok(tag) => {
                output.extend_from_slice(tag.as_ref());
                Output {
                    code: OK,
                    bytes: output,
                }
            }
            Err(_) => {
                output.zeroize();
                Output::error(LIMIT)
            }
        }
    } else {
        if input.len() < NONCE_BYTES + TAG_BYTES {
            return Output::error(AUTHENTICATION);
        }
        let nonce: [u8; NONCE_BYTES] = input[..NONCE_BYTES].try_into().unwrap();
        let mut output = input[NONCE_BYTES..].to_vec();
        match key.cipher.open_in_place(
            aead::Nonce::assume_unique_for_key(nonce),
            aead::Aad::from(aad),
            &mut output,
        ) {
            Ok(plaintext) => {
                let size = plaintext.len();
                output.truncate(size);
                Output {
                    code: OK,
                    bytes: output,
                }
            }
            Err(_) => {
                output.zeroize();
                Output::error(AUTHENTICATION)
            }
        }
    }
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __rt__crypto_aead_crypt(
    owner: *const u8,
    seal: bool,
    input: *const u8,
    len: usize,
    aad: *const u8,
    aad_len: usize,
) -> usize {
    let id = unsafe { owner_id(owner) };
    let key = keys()
        .lock()
        .unwrap_or_else(|p| p.into_inner())
        .entries
        .get(&id)
        .cloned();
    let result = match key {
        Some(key) => crypt(&key, seal, unsafe { bytes(input, len) }, unsafe {
            bytes(aad, aad_len)
        }),
        None => Output::error(CLOSED),
    };
    Box::into_raw(Box::new(result)) as usize
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __rt__crypto_output(
    id: usize,
    len: *mut usize,
    code: *mut u8,
) -> *const u8 {
    let output = unsafe { &*(id as *const Output) };
    unsafe {
        len.write(output.bytes.len());
        code.write(output.code)
    };
    output.bytes.as_ptr()
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __rt__crypto_output_close(id: usize) {
    let mut output = unsafe { Box::from_raw(id as *mut Output) };
    output.bytes.zeroize();
}

#[cfg(test)]
mod tests {
    use super::*;
    fn hex(s: &str) -> Vec<u8> {
        s.as_bytes()
            .chunks_exact(2)
            .map(|p| u8::from_str_radix(std::str::from_utf8(p).unwrap(), 16).unwrap())
            .collect()
    }
    fn key() -> Key {
        Key {
            cipher: aead::LessSafeKey::new(
                aead::UnboundKey::new(&aead::AES_256_GCM, &[0; 32]).unwrap(),
            ),
            messages: AtomicU64::new(0),
        }
    }
    #[test]
    fn sha_and_hmac_known_answers_and_verification() {
        let mut out = [0; 64];
        assert!(unsafe { __rt__crypto_digest(0, b"abc".as_ptr(), 3, out.as_mut_ptr()) });
        assert_eq!(
            &out[..32],
            hex("ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
        );
        assert!(unsafe { __rt__crypto_digest(1, b"abc".as_ptr(), 3, out.as_mut_ptr()) });
        assert_eq!(
            &out[..],
            hex(
                "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f"
            )
        );
        let key = [0x0b; 20];
        for (algorithm, answer) in [
            (
                0,
                "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7",
            ),
            (
                1,
                "87aa7cdea5ef619d4ff0b4241a1d6cb02379f4e2ce4ec2787ad0b30545e17cde daa833b7d6b8a702038b274eaea3f4e4be9d914eeb61f1702e696c203a126854",
            ),
        ] {
            let answer = hex(&answer.replace(' ', ""));
            assert!(unsafe {
                __rt__crypto_hmac(
                    algorithm,
                    key.as_ptr(),
                    key.len(),
                    b"Hi There".as_ptr(),
                    8,
                    out.as_mut_ptr(),
                )
            });
            assert_eq!(&out[..answer.len()], answer);
            assert!(unsafe {
                __rt__crypto_hmac_verify(
                    algorithm,
                    key.as_ptr(),
                    key.len(),
                    b"Hi There".as_ptr(),
                    8,
                    out.as_ptr(),
                    answer.len(),
                )
            });
            out[0] ^= 1;
            assert!(!unsafe {
                __rt__crypto_hmac_verify(
                    algorithm,
                    key.as_ptr(),
                    key.len(),
                    b"Hi There".as_ptr(),
                    8,
                    out.as_ptr(),
                    answer.len(),
                )
            });
        }
    }
    #[test]
    fn aes_gcm_known_answer_random_nonces_tampering_and_limit() {
        let key = key();
        // NIST empty-message AES-256-GCM vector: zero key and zero nonce.
        let mut vector = vec![0; 12];
        vector.extend(hex("530f8afbc74536b9a963b4f1c4cb738b"));
        let opened = crypt(&key, false, &vector, b"");
        assert_eq!(opened.code, OK);
        assert!(opened.bytes.is_empty());
        let first = crypt(&key, true, b"hello", b"metadata");
        let second = crypt(&key, true, b"hello", b"metadata");
        assert_eq!(first.code, OK);
        assert_eq!(second.code, OK);
        assert_ne!(&first.bytes[..12], &second.bytes[..12]);
        assert_eq!(
            crypt(&key, false, &first.bytes, b"metadata").bytes,
            b"hello"
        );
        assert_eq!(
            crypt(&key, false, &first.bytes, b"wrong").code,
            AUTHENTICATION
        );
        let mut forged = first.bytes.clone();
        *forged.last_mut().unwrap() ^= 1;
        let failed = crypt(&key, false, &forged, b"metadata");
        assert_eq!(failed.code, AUTHENTICATION);
        assert!(failed.bytes.is_empty());
        key.messages.store(MESSAGE_LIMIT - 1, Ordering::SeqCst);
        assert_eq!(crypt(&key, true, b"", b"").code, OK);
        assert_eq!(crypt(&key, true, b"", b"").code, LIMIT);
    }
    #[test]
    fn entropy_empty_and_constant_time_equality_boundaries() {
        assert!(unsafe { __rt__crypto_random(std::ptr::null_mut(), 0) });
        assert!(unsafe { __rt__crypto_equal(b"ab".as_ptr(), 2, b"ab".as_ptr(), 2) });
        assert!(!unsafe { __rt__crypto_equal(b"ab".as_ptr(), 2, b"ac".as_ptr(), 2) });
        assert!(!unsafe { __rt__crypto_equal(b"ab".as_ptr(), 2, b"abx".as_ptr(), 3) });
    }
}
