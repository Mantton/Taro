//! Byte encoding for metadata payloads and stack-map descriptors.
//!
//! Integers, enum tags and lengths are variable-length, so the small values
//! that dominate these files (local and block indices, line numbers, table
//! references, enum tags) take one byte instead of four or eight. Trailing
//! bytes after a value are rejected.

use bincode::Options;
use serde::{Deserialize, Serialize};

fn options() -> impl Options {
    bincode::DefaultOptions::new()
}

pub(crate) fn encode<T: Serialize + ?Sized>(value: &T) -> bincode::Result<Vec<u8>> {
    options().serialize(value)
}

pub(crate) fn decode<'de, T: Deserialize<'de>>(bytes: &'de [u8]) -> bincode::Result<T> {
    options().deserialize(bytes)
}

#[cfg(test)]
mod tests {
    #[test]
    fn small_integers_take_one_byte() {
        assert_eq!(super::encode(&7u32).unwrap(), [7]);
        assert_eq!(super::encode(&vec![1u64, 2, 3]).unwrap(), [3, 1, 2, 3]);
    }

    #[test]
    fn trailing_bytes_are_rejected() {
        let mut bytes = super::encode(&5u32).unwrap();
        bytes.push(0);
        assert!(super::decode::<u32>(&bytes).is_err());
    }
}
