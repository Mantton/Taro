//! Seeded mutational byte fuzzer backing `taro test --fuzz <target>`.
//!
//! Uses a deterministic PRNG (`SplitMix64`) and an in-process catch-unwind
//! boundary so any panic or assertion failure inside a `@fuzz` target is
//! intercepted, saved as a raw byte artifact under an ignored output
//! directory, and reported with an exact `--fuzz-replay` command.

use std::{
    fs,
    io::Write,
    path::{Path, PathBuf},
};

use crate::panic_unwind::{catch_harness_panic, finish_unexpected_harness_panic};

const DEFAULT_SEED: u64 = 0x5441_524f_4655_5a5a; // "TAROFUZZ"
const DEFAULT_RUNS: u64 = 1000;
const DEFAULT_MAX_LEN: usize = 4096;
const MAX_CORPUS_ENTRIES: usize = 256;

struct SplitMix64 {
    state: u64,
}

impl SplitMix64 {
    fn new(seed: u64) -> Self {
        Self { state: seed }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn next_usize(&mut self, bound: usize) -> usize {
        if bound <= 1 {
            return 0;
        }
        (self.next_u64() as usize) % bound
    }

    fn next_u8(&mut self) -> u8 {
        self.next_u64() as u8
    }
}

fn default_seeds() -> Vec<Vec<u8>> {
    vec![
        Vec::new(),
        vec![0],
        vec![0xff],
        b"0".to_vec(),
        b"-1".to_vec(),
        b"1234567890".to_vec(),
        b"true".to_vec(),
        b"{}".to_vec(),
        b"[]".to_vec(),
        b"\"\"".to_vec(),
        b"\n\r\t ".to_vec(),
        b"hello".to_vec(),
        vec![0x7f, 0x80, 0x00, 0xff],
    ]
}

fn mutate_input(rng: &mut SplitMix64, corpus: &[Vec<u8>], max_len: usize, iteration: u64) -> Vec<u8> {
    if max_len == 0 {
        return Vec::new();
    }
    // Early iterations bias toward small fresh/mutated inputs so common edge
    // cases trigger rapidly before exploring larger buffers.
    let cap = if iteration < 64 {
        max_len.min(32)
    } else if iteration < 256 {
        max_len.min(128)
    } else {
        max_len
    };

    let mut data = if corpus.is_empty() || rng.next_usize(4) == 0 {
        let len = rng.next_usize(cap + 1);
        let mut fresh = Vec::with_capacity(len);
        for _ in 0..len {
            fresh.push(rng.next_u8());
        }
        return fresh;
    } else {
        corpus[rng.next_usize(corpus.len())].clone()
    };

    if data.len() > cap {
        data.truncate(cap);
    }

    let mutations = 1 + rng.next_usize(4);
    for _ in 0..mutations {
        match rng.next_usize(7) {
            // Flip a single bit.
            0 if !data.is_empty() => {
                let idx = rng.next_usize(data.len());
                let bit = 1u8 << rng.next_usize(8);
                data[idx] ^= bit;
            }
            // Replace one byte with a random or boundary byte.
            1 if !data.is_empty() => {
                let idx = rng.next_usize(data.len());
                const INTERESTING: &[u8] = &[0x00, 0x01, 0x09, 0x0a, 0x20, 0x2d, 0x30, 0x7f, 0x80, 0xff];
                data[idx] = if rng.next_usize(2) == 0 {
                    INTERESTING[rng.next_usize(INTERESTING.len())]
                } else {
                    rng.next_u8()
                };
            }
            // Insert 1..=8 bytes.
            2 if data.len() < cap => {
                let insert_len = (1 + rng.next_usize(8)).min(cap - data.len());
                let pos = rng.next_usize(data.len() + 1);
                for offset in 0..insert_len {
                    let b = rng.next_u8();
                    data.insert(pos + offset, b);
                }
            }
            // Erase a slice.
            3 if !data.is_empty() => {
                let start = rng.next_usize(data.len());
                let max_del = (data.len() - start).min(8).max(1);
                let del_len = 1 + rng.next_usize(max_del);
                data.drain(start..start + del_len);
            }
            // Splice with another corpus entry.
            4 if !corpus.is_empty() => {
                let other = &corpus[rng.next_usize(corpus.len())];
                if !other.is_empty() && data.len() < cap {
                    let split = rng.next_usize(data.len() + 1);
                    let other_start = rng.next_usize(other.len());
                    let take = (other.len() - other_start).min(cap - data.len());
                    data.splice(split..split, other[other_start..other_start + take].iter().copied());
                }
            }
            // Overwrite a short printable ASCII chunk.
            5 if data.len() < cap => {
                let chunk_len = (1 + rng.next_usize(8)).min(cap - data.len());
                for _ in 0..chunk_len {
                    data.push(0x20 + (rng.next_u8() % 95));
                }
            }
            // Duplicate existing content.
            6 if !data.is_empty() && data.len() < cap => {
                let dup_len = data.len().min(cap - data.len());
                let copy: Vec<u8> = data[..dup_len].to_vec();
                data.extend_from_slice(&copy);
            }
            _ => {}
        }
    }

    data
}

fn fnv1a_hash(bytes: &[u8]) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for &b in bytes {
        h ^= b as u64;
        h = h.wrapping_mul(0x0000_0100_0000_01b3);
    }
    h
}

fn sanitize_filename_component(name: &str) -> String {
    name.chars()
        .map(|c| if c.is_ascii_alphanumeric() || c == '_' || c == '-' { c } else { '_' })
        .collect()
}

fn format_hex_preview(bytes: &[u8]) -> String {
    let shown = bytes.len().min(64);
    let mut out = String::with_capacity(shown * 3 + 16);
    for (idx, b) in bytes[..shown].iter().enumerate() {
        if idx > 0 {
            out.push(' ');
        }
        use std::fmt::Write;
        let _ = write!(out, "{b:02x}");
    }
    if bytes.len() > shown {
        out.push_str(&format!(" ... ({} bytes total)", bytes.len()));
    }
    out
}

fn save_crash_artifact(artifacts_dir: &Path, target_name: &str, input: &[u8]) -> Result<PathBuf, String> {
    fs::create_dir_all(artifacts_dir)
        .map_err(|e| format!("failed to create fuzz artifacts dir '{}': {e}", artifacts_dir.display()))?;
    let safe_target = sanitize_filename_component(target_name);
    let hash = fnv1a_hash(input);
    let path = artifacts_dir.join(format!("crash-{safe_target}-{hash:016x}.bin"));
    fs::write(&path, input)
        .map_err(|e| format!("failed to write failing fuzz input '{}': {e}", path.display()))?;
    Ok(path)
}

fn run_single_input(
    callback: extern "C-unwind" fn(*const u8, usize),
    input: &[u8],
) -> bool {
    let ptr = input.as_ptr();
    let len = input.len();
    catch_harness_panic(|| {
        callback(ptr, len);
    })
}

fn parse_env_u64(key: &str, default: u64) -> u64 {
    std::env::var(key)
        .ok()
        .and_then(|v| v.trim().parse::<u64>().ok())
        .unwrap_or(default)
}

fn parse_env_usize(key: &str, default: usize) -> usize {
    std::env::var(key)
        .ok()
        .and_then(|v| v.trim().parse::<usize>().ok())
        .unwrap_or(default)
}

/// Entry point invoked by the compiler-generated fuzz harness (`taro_start`).
///
/// Returns `0` when all fuzz runs (or the replayed input) pass without panic,
/// or `101` when a failing input is discovered or replay fails.
#[unsafe(no_mangle)]
pub extern "C" fn __rt__fuzz_run(
    name_ptr: *const u8,
    name_len: usize,
    callback: extern "C-unwind" fn(*const u8, usize),
) -> i32 {
    let target_name = if name_ptr.is_null() || name_len == 0 {
        String::from("<fuzz>")
    } else {
        let bytes = unsafe { std::slice::from_raw_parts(name_ptr, name_len) };
        String::from_utf8_lossy(bytes).into_owned()
    };

    let target_path = std::env::var("TARO_FUZZ_TARGET_PATH").unwrap_or_else(|_| ".".to_string());
    let artifacts_dir = std::env::var("TARO_FUZZ_ARTIFACTS_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|_| PathBuf::from("target/fuzz-artifacts"));

    // Replay mode: execute one specific saved input file and report result.
    if let Ok(replay_path_raw) = std::env::var("TARO_FUZZ_REPLAY") {
        let replay_path = PathBuf::from(replay_path_raw);
        let bytes = match fs::read(&replay_path) {
            Ok(bytes) => bytes,
            Err(err) => {
                let _ = writeln!(
                    std::io::stderr(),
                    "error: failed to read fuzz replay input '{}': {err}",
                    replay_path.display()
                );
                return 101;
            }
        };
        let panicked = run_single_input(callback, &bytes);
        if panicked {
            let _ = writeln!(
                std::io::stdout(),
                "fuzz replay {} on {} ... FAILED (panicked, {} bytes)",
                replay_path.display(),
                target_name,
                bytes.len()
            );
            let _ = std::io::stdout().flush();
            let _ = writeln!(
                std::io::stderr(),
                "  input hex: [{}]",
                format_hex_preview(&bytes)
            );
            finish_unexpected_harness_panic();
            return 101;
        }
        let _ = writeln!(
            std::io::stdout(),
            "fuzz replay {} on {} ... ok ({} bytes)",
            replay_path.display(),
            target_name,
            bytes.len()
        );
        return 0;
    }

    let seed = parse_env_u64("TARO_FUZZ_SEED", DEFAULT_SEED);
    let runs = parse_env_u64("TARO_FUZZ_RUNS", DEFAULT_RUNS);
    let max_len = parse_env_usize("TARO_FUZZ_MAX_LEN", DEFAULT_MAX_LEN);

    let _ = writeln!(
        std::io::stdout(),
        "\nfuzzing {} (runs={}, seed={}, max_len={})",
        target_name,
        runs,
        seed,
        max_len
    );
    let _ = std::io::stdout().flush();

    let mut rng = SplitMix64::new(seed);
    let mut corpus = default_seeds();

    // Load any optional user seeds from `<artifacts_dir>/corpus`.
    let corpus_dir = artifacts_dir.join("corpus");
    if let Ok(entries) = fs::read_dir(&corpus_dir) {
        let mut paths: Vec<PathBuf> = entries
            .flatten()
            .map(|e| e.path())
            .filter(|p| p.is_file())
            .collect();
        paths.sort();
        for path in paths {
            if let Ok(mut bytes) = fs::read(&path) {
                if bytes.len() > max_len {
                    bytes.truncate(max_len);
                }
                corpus.push(bytes);
            }
        }
    }

    for i in 0..runs {
        let input = if (i as usize) < corpus.len() {
            let mut seed_entry = corpus[i as usize].clone();
            if seed_entry.len() > max_len {
                seed_entry.truncate(max_len);
            }
            seed_entry
        } else {
            mutate_input(&mut rng, &corpus, max_len, i)
        };

        let panicked = run_single_input(callback, &input);
        if panicked {
            let _ = writeln!(
                std::io::stdout(),
                "fuzz target {} ... FAILED on run {} (seed={}, len={})",
                target_name,
                i + 1,
                seed,
                input.len()
            );
            let _ = std::io::stdout().flush();
            let _ = writeln!(
                std::io::stderr(),
                "  input hex: [{}]",
                format_hex_preview(&input)
            );
            match save_crash_artifact(&artifacts_dir, &target_name, &input) {
                Ok(saved) => {
                    let _ = writeln!(
                        std::io::stderr(),
                        "  failing input saved to: {}",
                        saved.display()
                    );
                    let _ = writeln!(
                        std::io::stderr(),
                        "  replay with: taro test {} --fuzz {} --fuzz-replay {}",
                        target_path,
                        target_name,
                        saved.display()
                    );
                }
                Err(err) => {
                    let _ = writeln!(std::io::stderr(), "  warning: {err}");
                }
            }
            finish_unexpected_harness_panic();
            return 101;
        }

        if (i as usize) >= corpus.len() && corpus.len() < MAX_CORPUS_ENTRIES && i % 16 == 0 {
            corpus.push(input);
        }
    }

    let _ = writeln!(
        std::io::stdout(),
        "fuzz target {} ... ok ({} runs, seed={})",
        target_name,
        runs,
        seed
    );
    0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn splitmix64_is_deterministic_for_fixed_seed() {
        let mut a = SplitMix64::new(42);
        let mut b = SplitMix64::new(42);
        let seq_a: Vec<u64> = (0..16).map(|_| a.next_u64()).collect();
        let seq_b: Vec<u64> = (0..16).map(|_| b.next_u64()).collect();
        assert_eq!(seq_a, seq_b);
    }

    #[test]
    fn mutate_input_respects_max_len_and_is_reproducible() {
        let corpus = default_seeds();
        let mut r1 = SplitMix64::new(12345);
        let mut r2 = SplitMix64::new(12345);
        for i in 0..50 {
            let v1 = mutate_input(&mut r1, &corpus, 64, i);
            let v2 = mutate_input(&mut r2, &corpus, 64, i);
            assert_eq!(v1, v2);
            assert!(v1.len() <= 64);
        }
    }
}
