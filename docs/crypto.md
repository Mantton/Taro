# Cryptography

`std::crypto` exposes standard primitives through the maintained
[ring](https://docs.rs/ring/latest/ring/) backend already used by TLS. It includes
OS-backed random bytes, SHA-256/SHA-512, full-length HMAC-SHA-256/HMAC-SHA-512,
constant-time content comparison and AES-256-GCM authenticated encryption.
SHA/HMAC outputs are raw fixed-size byte arrays; hexadecimal/base64 encoding is
an explicit operation in `std::encoding`.

```taro
import std::crypto::{aesgcm, random, sha256, hmac}
import std::mem::Span

text := "Hello, World!"
digest := sha256::sum(text)
key := aesgcm::Key::generate().unwrap()
defer { key.close() }
packet := key.seal(Span[uint8]::fromString(&text)).unwrap()
plaintext := key.open(packet.asSpan()).unwrap()
```

`random::fill(span)` fills writable storage, while `random::bytes(count)` returns
an ordinary mutable List with fresh ownership. Random-source failure returns
`Error.entropy`; fill may have modified part of its destination. Hashes borrow
their input only for the call. `hmac::sha256(key, data)` and `hmac::sha512` produce
full tags; the matching `verifySha256`/`verifySha512` functions use the provider's
verification routine and reject truncated tags. `subtle::equal(left, right)`
compares contents in constant time when lengths match. Lengths are public.

## Authenticated encryption

The initial encryption API follows Go's
[NewGCMWithRandomNonce](https://pkg.go.dev/crypto/cipher#NewGCMWithRandomNonce).
`aesgcm::Key::new(span)` snapshots exactly 32 key bytes; `generate()` creates a
key directly in native storage. `seal` draws a fresh 12-byte nonce and returns:

```
12-byte nonce | ciphertext | 16-byte authentication tag
```

`seal(plaintext, additionalData: aad)` authenticates the additional bytes without
encrypting them. `open(packet, additionalData: aad)` requires the same bytes and
returns `Error.authentication` on tampering, truncation or an incorrect key/AAD.
Plaintext is copied into managed output only after authentication succeeds.
The packet has no algorithm/version identifier: its enclosing protocol must
identify AES-256-GCM. It interoperates with Go's random-nonce GCM and standard
AES-GCM implementations that take the nonce separately.

As specified by Go, a key must encrypt at most 2^32 messages in its entire
lifetime. Shared key copies share a native counter and close state; the counter
rejects further seals at that bound. Importing the same key again, using it in
another process or restarting does not reset the *key material's* lifetime
budget. Applications must rotate persisted/shared keys accordingly. Imported
keys are raw keys, not passwords; no implicit password derivation occurs.

Key memory is automatically reclaimed by GC. Optional close prevents new
operations through aliases and releases the native key early;
an already accepted native operation retains its key until completion. Native
temporary plaintext/result buffers and imported/generated key staging bytes
are cleared on release. Caller-owned key/plaintext storage follows normal Taro
GC semantics and is not promised to be immediately erased.

Rust's std has no corresponding crypto module; established crates such as
[RustCrypto AES-GCM](https://docs.rs/aes-gcm/latest/aes_gcm/) expose the same
standard algorithm. Explicit-nonce protocol APIs, streaming hash contexts,
password derivation, signatures and key agreement are separate additions.
Crypto is synchronous; native calls use the existing blocking boundary so GC
can proceed while input roots remain published. Key creation uses the existing GC callback boundary to allocate its collected
native owner. CPU-heavy crypto belongs in an
appropriate application task/blocking workload.

Focused tests cover published SHA/HMAC/NIST vectors, authentication failure,
nonce separation, key-close aliases, message limits and concurrent GC. These
wrapper tests do not constitute an independent cryptographic security audit.
