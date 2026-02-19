//! Hash seed runtime exports.
//!
//! Seeds are generated once per process using Rust std random state and then
//! cached for stable reuse within the process.

use std::{
    collections::hash_map::RandomState,
    hash::{BuildHasher, Hasher},
    sync::OnceLock,
};

#[derive(Clone, Copy)]
struct HashSeeds {
    seed0: u64,
    seed1: u64,
}

fn initialize_hash_seeds() -> HashSeeds {
    let random_state = RandomState::new();

    let mut seed0_hasher = random_state.build_hasher();
    seed0_hasher.write_u64(0x0706_0504_0302_0100);
    let seed0 = seed0_hasher.finish();

    let mut seed1_hasher = random_state.build_hasher();
    seed1_hasher.write_u64(0x0f0e_0d0c_0b0a_0908);
    let seed1 = seed1_hasher.finish();

    HashSeeds { seed0, seed1 }
}

fn process_hash_seeds() -> &'static HashSeeds {
    static HASH_SEEDS: OnceLock<HashSeeds> = OnceLock::new();
    HASH_SEEDS.get_or_init(initialize_hash_seeds)
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__hash_seed0() -> u64 {
    process_hash_seeds().seed0
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__hash_seed1() -> u64 {
    process_hash_seeds().seed1
}
