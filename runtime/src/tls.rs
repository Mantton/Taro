//! rustls owns cryptography and bounded record state, while std.tls drives
//! records over the existing Taro reactor. No managed pointer escapes a call.
use crate::panic_unwind::RtString;
use rustls::pki_types::{CertificateDer, PrivateKeyDer, ServerName, pem::PemObject};
use rustls_platform_verifier::BuilderVerifierExt;
use std::collections::HashMap;
use std::io::{Cursor, Read, Write};
use std::sync::{Arc, Mutex, OnceLock};

enum Config {
    Client(Arc<rustls::ClientConfig>),
    Server(Arc<rustls::ServerConfig>),
}
#[derive(Default)]
struct Registry {
    next: usize,
    configs: HashMap<usize, Config>,
    sessions: HashMap<usize, Arc<Mutex<rustls::Connection>>>,
}
impl Registry {
    fn id(&mut self) -> Option<usize> {
        self.next = self.next.checked_add(1)?;
        Some(self.next)
    }
}
fn registry() -> &'static Mutex<Registry> {
    static TABLE: OnceLock<Mutex<Registry>> = OnceLock::new();
    TABLE.get_or_init(Default::default)
}
unsafe fn bytes<'a>(value: RtString) -> &'a [u8] {
    if value.len == 0 {
        &[]
    } else {
        unsafe { std::slice::from_raw_parts(value.ptr, value.len) }
    }
}
fn config(server: bool, certs: &[u8], key: &[u8]) -> Result<Config, Box<dyn std::error::Error>> {
    let provider = Arc::new(rustls::crypto::ring::default_provider());
    let certificates = CertificateDer::pem_slice_iter(certs).collect::<Result<Vec<_>, _>>()?;
    if server {
        let key = PrivateKeyDer::from_pem_slice(key)?;
        let mut config = rustls::ServerConfig::builder_with_provider(provider)
            .with_safe_default_protocol_versions()?
            .with_no_client_auth()
            .with_single_cert(certificates, key)?;
        config.alpn_protocols = vec![b"http/1.1".to_vec()];
        Ok(Config::Server(Arc::new(config)))
    } else {
        let builder = rustls::ClientConfig::builder_with_provider(provider)
            .with_safe_default_protocol_versions()?;
        let mut config = if certs.is_empty() {
            builder.with_platform_verifier()?.with_no_client_auth()
        } else {
            let mut roots = rustls::RootCertStore::empty();
            for cert in certificates {
                roots.add(cert)?;
            }
            if roots.is_empty() {
                return Err("empty TLS trust roots".into());
            }
            builder.with_root_certificates(roots).with_no_client_auth()
        };
        config.alpn_protocols = vec![b"http/1.1".to_vec()];
        Ok(Config::Client(Arc::new(config)))
    }
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __rt__tls_config(server: bool, certs: RtString, key: RtString) -> usize {
    let Ok(config) = config(server, unsafe { bytes(certs) }, unsafe { bytes(key) }) else {
        return 0;
    };
    let mut table = registry().lock().unwrap_or_else(|p| p.into_inner());
    let Some(id) = table.id() else { return 0 };
    table.configs.insert(id, config);
    id
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __rt__tls_session(config: usize, host: RtString) -> usize {
    let mut table = registry().lock().unwrap_or_else(|p| p.into_inner());
    let connection = match table.configs.get(&config) {
        Some(Config::Server(config)) => {
            rustls::ServerConnection::new(config.clone()).map(rustls::Connection::Server)
        }
        Some(Config::Client(config)) => {
            let Ok(host) = std::str::from_utf8(unsafe { bytes(host) }) else {
                return 0;
            };
            let Ok(name) = ServerName::try_from(host.to_owned()) else {
                return 0;
            };
            rustls::ClientConnection::new(config.clone(), name).map(rustls::Connection::Client)
        }
        None => return 0,
    };
    let Ok(mut connection) = connection else {
        return 0;
    };
    connection.set_buffer_limit(Some(32 * 1024));
    let Some(id) = table.id() else { return 0 };
    table.sessions.insert(id, Arc::new(Mutex::new(connection)));
    id
}
#[unsafe(no_mangle)]
pub extern "C" fn __rt__tls_close(id: usize) {
    let mut table = registry().lock().unwrap_or_else(|p| p.into_inner());
    table.sessions.remove(&id);
    table.configs.remove(&id);
}
/// -2 = plaintext temporarily unavailable; -1 = closed/protocol error.
/// Slices are borrowed only for this synchronous call, including record parsing.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __rt__tls_step(id: usize, op: u8, data: *mut u8, len: usize) -> isize {
    let connection = registry()
        .lock()
        .unwrap_or_else(|p| p.into_inner())
        .sessions
        .get(&id)
        .cloned();
    let Some(connection) = connection else {
        return -1;
    };
    let mut connection = connection.lock().unwrap_or_else(|p| p.into_inner());
    let buffer = if len == 0 {
        &mut [][..]
    } else {
        unsafe { std::slice::from_raw_parts_mut(data, len) }
    };
    let result = match op {
        0 => return isize::from(connection.is_handshaking()),
        1 => connection
            .read_tls(&mut Cursor::new(&*buffer))
            .and_then(|n| {
                connection
                    .process_new_packets()
                    .map(|_| n)
                    .map_err(std::io::Error::other)
            }),
        2 => connection.write_tls(&mut Cursor::new(buffer)),
        3 => connection.reader().read(buffer),
        4 => connection.writer().write(buffer),
        5 => connection.read_tls(&mut std::io::empty()),
        _ => return -1,
    };
    match result {
        Ok(n) => n as isize,
        Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => -2,
        Err(_) => -1,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn rejects_invalid_credentials_and_closed_handles() {
        assert!(config(true, b"", b"").is_err());
        assert!(config(false, b"invalid", b"").is_err());
        assert_eq!(
            unsafe { __rt__tls_step(usize::MAX, 0, std::ptr::null_mut(), 0) },
            -1
        );
    }
}

#[cfg(test)]
mod record_tests {
    use super::*;
    use rustls::pki_types::PrivatePkcs8KeyDer;
    #[test]
    fn bounded_record_abi_handshakes_and_transfers_plaintext() {
        let provider = Arc::new(rustls::crypto::ring::default_provider());
        let certificate = CertificateDer::from(
            include_bytes!("../tests/fixtures/http-localhost-cert.der").to_vec(),
        );
        let key = PrivateKeyDer::Pkcs8(PrivatePkcs8KeyDer::from(
            include_bytes!("../tests/fixtures/http-localhost-key.der").to_vec(),
        ));
        let server = rustls::ServerConfig::builder_with_provider(provider.clone())
            .with_safe_default_protocol_versions()
            .unwrap()
            .with_no_client_auth()
            .with_single_cert(vec![certificate.clone()], key)
            .unwrap();
        let mut roots = rustls::RootCertStore::empty();
        roots.add(certificate).unwrap();
        let client = rustls::ClientConfig::builder_with_provider(provider)
            .with_safe_default_protocol_versions()
            .unwrap()
            .with_root_certificates(roots)
            .with_no_client_auth();
        let (server_id, client_id) = {
            let mut table = registry().lock().unwrap();
            let s = table.id().unwrap();
            table.configs.insert(s, Config::Server(Arc::new(server)));
            let c = table.id().unwrap();
            table.configs.insert(c, Config::Client(Arc::new(client)));
            (s, c)
        };
        let host = RtString {
            ptr: b"localhost".as_ptr(),
            len: 9,
        };
        let server = unsafe { __rt__tls_session(server_id, host) };
        let client = unsafe { __rt__tls_session(client_id, host) };
        __rt__tls_close(server_id);
        __rt__tls_close(client_id);
        assert_ne!(server, 0);
        assert_ne!(client, 0);
        let mut buffer = [0u8; 4096];
        for _ in 0..100 {
            for (from, to) in [(client, server), (server, client)] {
                loop {
                    let n = unsafe { __rt__tls_step(from, 2, buffer.as_mut_ptr(), buffer.len()) };
                    assert!(n >= 0);
                    if n == 0 {
                        break;
                    }
                    let mut used = 0;
                    while used < n as usize {
                        let count = unsafe {
                            __rt__tls_step(to, 1, buffer.as_mut_ptr().add(used), n as usize - used)
                        };
                        assert!(count > 0);
                        used += count as usize;
                    }
                }
            }
            if unsafe { __rt__tls_step(client, 0, buffer.as_mut_ptr(), 0) } == 0
                && unsafe { __rt__tls_step(server, 0, buffer.as_mut_ptr(), 0) } == 0
            {
                break;
            }
        }
        assert_eq!(
            unsafe { __rt__tls_step(client, 0, buffer.as_mut_ptr(), 0) },
            0
        );
        buffer[..5].copy_from_slice(b"hello");
        assert_eq!(
            unsafe { __rt__tls_step(client, 4, buffer.as_mut_ptr(), 5) },
            5
        );
        let n = unsafe { __rt__tls_step(client, 2, buffer.as_mut_ptr(), buffer.len()) };
        assert!(n > 5);
        assert_eq!(
            unsafe { __rt__tls_step(server, 1, buffer.as_mut_ptr(), n as usize) },
            n
        );
        assert_eq!(
            unsafe { __rt__tls_step(server, 3, buffer.as_mut_ptr(), buffer.len()) },
            5
        );
        assert_eq!(&buffer[..5], b"hello");
        __rt__tls_close(client);
        __rt__tls_close(server);
        assert_eq!(
            unsafe { __rt__tls_step(client, 0, buffer.as_mut_ptr(), 0) },
            -1
        );
    }
}
