//! Versioned private protocol between the editor server and its worker.

use std::{
    collections::BTreeMap,
    io::{self, Read, Write},
    path::PathBuf,
    sync::Arc,
};

use compiler::compile::analysis_products::AnalysisProduct;
use serde::{Deserialize, Serialize, de::DeserializeOwned};

const SCHEMA: u16 = 2;
pub const MAX_FRAME: usize = 128 * 1024 * 1024;

#[derive(Debug, Serialize, Deserialize)]
pub enum AnalysisMode {
    Package,
    Body,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct Stamp {
    pub generation: u64,
    pub revision: u64,
}

#[derive(Debug, Serialize, Deserialize)]
pub enum ToWorker {
    Analyze(AnalysisRequest),
    Cancel { revision: u64 },
}

#[derive(Debug, Serialize, Deserialize)]
pub struct AnalysisRequest {
    pub stamp: Stamp,
    pub inputs: Inputs,
}

#[derive(Debug, Serialize, Deserialize)]
pub enum Inputs {
    Reset {
        root: PathBuf,
        documents: BTreeMap<PathBuf, String>,
    },
    Delta(BTreeMap<PathBuf, Option<String>>),
}

#[derive(Debug, Serialize, Deserialize)]
pub enum FromWorker {
    Finished {
        stamp: Stamp,
        mode: AnalysisMode,
        result: Result<Arc<AnalysisProduct>, String>,
    },
    Cancelled(Stamp),
    Rejected {
        stamp: Stamp,
        error: String,
    },
}

impl FromWorker {
    pub fn stamp(&self) -> Stamp {
        match self {
            Self::Finished { stamp, .. }
            | Self::Rejected { stamp, .. }
            | Self::Cancelled(stamp) => *stamp,
        }
    }
}

#[derive(Serialize, Deserialize)]
struct Frame<T> {
    schema: u16,
    data: T,
}

pub fn read<T: DeserializeOwned>(input: &mut impl Read) -> io::Result<Option<T>> {
    let mut header = [0; 4];
    if input.read(&mut header[..1])? == 0 {
        return Ok(None);
    }
    input.read_exact(&mut header[1..])?;
    let length = u32::from_be_bytes(header) as usize;
    if length == 0 || length > MAX_FRAME {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "invalid worker message length",
        ));
    }
    let mut data = vec![0; length];
    input.read_exact(&mut data)?;
    let frame: Frame<T> = serde_json::from_slice(&data)?;
    if frame.schema != SCHEMA {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "worker protocol version mismatch",
        ));
    }
    Ok(Some(frame.data))
}

pub fn write<T: Serialize>(output: &mut impl Write, data: &T) -> io::Result<()> {
    let frame = encode(data, MAX_FRAME)?.ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            "worker message exceeds frame limit",
        )
    })?;
    write_frame(output, &frame)
}

/// The encoded frame, or `None` when it would exceed `limit` bytes.
pub fn encode<T: Serialize>(data: &T, limit: usize) -> io::Result<Option<Vec<u8>>> {
    let frame = serde_json::to_vec(&Frame {
        schema: SCHEMA,
        data,
    })?;
    Ok((frame.len() <= limit.min(MAX_FRAME)).then_some(frame))
}

pub fn write_frame(output: &mut impl Write, frame: &[u8]) -> io::Result<()> {
    output.write_all(&(frame.len() as u32).to_be_bytes())?;
    output.write_all(frame)?;
    output.flush()
}

/// A reply that fits the frame limit. An analysis too large to send becomes
/// an error for that revision instead of ending the worker, which would be
/// restarted into the same failure.
pub fn reply_frame(reply: &FromWorker, limit: usize) -> io::Result<Vec<u8>> {
    if let Some(frame) = encode(reply, limit)? {
        return Ok(frame);
    }
    let error = FromWorker::Finished {
        stamp: reply.stamp(),
        mode: AnalysisMode::Package,
        result: Err(format!(
            "the analysis result exceeds the {} MiB worker message limit",
            limit / (1024 * 1024)
        )),
    };
    encode(&error, MAX_FRAME)?.ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            "error reply exceeds frame limit",
        )
    })
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use compiler::compile::analysis_products::AnalysisProduct;

    use super::{AnalysisMode, FromWorker, Stamp};

    #[test]
    fn an_oversized_analysis_becomes_an_error_reply() {
        let stamp = Stamp {
            generation: 3,
            revision: 7,
        };
        let product: AnalysisProduct = serde_json::from_value(serde_json::json!({
            "revision": 7, "complete": true, "syntax_uncertainty": "None",
            "declarations": [], "bodies": [], "occurrences": [],
            "missing_members": [], "diagnostics": [],
        }))
        .unwrap();
        let reply = FromWorker::Finished {
            stamp,
            mode: AnalysisMode::Body,
            result: Ok(Arc::new(product)),
        };
        let full = super::encode(&reply, usize::MAX).unwrap().unwrap();
        let frame = super::reply_frame(&reply, full.len() - 1).unwrap();
        let mut bytes = Vec::new();
        super::write_frame(&mut bytes, &frame).unwrap();
        match super::read::<FromWorker>(&mut bytes.as_slice()).unwrap() {
            Some(FromWorker::Finished {
                stamp: sent,
                result: Err(error),
                ..
            }) => {
                assert_eq!(sent, stamp);
                assert!(error.contains("message limit"), "{error}");
            }
            _ => panic!("an error reply for the same revision"),
        }
        assert_eq!(super::reply_frame(&reply, full.len()).unwrap(), full);
    }

    #[test]
    fn frames_reject_truncation_size_and_version_mismatch() {
        let mut bytes = Vec::new();
        super::write(
            &mut bytes,
            &FromWorker::Cancelled(Stamp {
                generation: 1,
                revision: 2,
            }),
        )
        .unwrap();
        match super::read(&mut bytes.as_slice()).unwrap() {
            Some(FromWorker::Cancelled(stamp)) => assert_eq!(stamp.revision, 2),
            _ => panic!("cancelled reply"),
        }
        assert!(super::read::<FromWorker>(&mut &bytes[..bytes.len() - 1]).is_err());
        bytes[0] = 255;
        assert!(super::read::<FromWorker>(&mut bytes.as_slice()).is_err());
        let mut wrong = Vec::new();
        super::write(
            &mut wrong,
            &FromWorker::Cancelled(Stamp {
                generation: 1,
                revision: 2,
            }),
        )
        .unwrap();
        let version = wrong
            .windows(10)
            .position(|window| window == b"\"schema\":2")
            .unwrap()
            + 9;
        wrong[version] = b'9';
        assert!(super::read::<FromWorker>(&mut wrong.as_slice()).is_err());
    }
}
