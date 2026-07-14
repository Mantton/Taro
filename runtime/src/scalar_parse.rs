//! Locale-independent scalar parsing helpers used by `std.convert`.
//!
//! Taro's standard library validates its public decimal grammar and reports
//! byte-accurate syntax errors. These shims provide Rust's correctly-rounded
//! IEEE-754 conversion without inheriting process locale behavior from libc.

use crate::panic_unwind::RtString;

const PARSE_OK: u8 = 0;
const PARSE_INVALID: u8 = 1;
const PARSE_OVERFLOW: u8 = 2;
const PARSE_UNDERFLOW: u8 = 3;

fn with_input_bytes<T>(input: RtString, use_bytes: impl FnOnce(&[u8]) -> T) -> Option<T> {
    if input.len == 0 {
        return Some(use_bytes(&[]));
    }
    if input.ptr.is_null() {
        return None;
    }

    // Taro strings remain live for the duration of the synchronous runtime
    // call. The returned slice never escapes the call site.
    let bytes = unsafe { std::slice::from_raw_parts(input.ptr, input.len) };
    Some(use_bytes(bytes))
}

fn significand_is_nonzero(bytes: &[u8]) -> bool {
    for byte in bytes {
        if *byte == b'e' || *byte == b'E' {
            break;
        }
        if matches!(*byte, b'1'..=b'9') {
            return true;
        }
    }
    false
}

fn parse_f32_bits(bytes: &[u8]) -> Result<u32, u8> {
    let text = std::str::from_utf8(bytes).map_err(|_| PARSE_INVALID)?;
    let value = text.parse::<f32>().map_err(|_| PARSE_INVALID)?;

    if value.is_nan() {
        return Err(PARSE_INVALID);
    }
    if value.is_infinite() {
        return Err(PARSE_OVERFLOW);
    }
    if value == 0.0 && significand_is_nonzero(bytes) {
        return Err(PARSE_UNDERFLOW);
    }
    Ok(value.to_bits())
}

fn parse_f64_bits(bytes: &[u8]) -> Result<u64, u8> {
    let text = std::str::from_utf8(bytes).map_err(|_| PARSE_INVALID)?;
    let value = text.parse::<f64>().map_err(|_| PARSE_INVALID)?;

    if value.is_nan() {
        return Err(PARSE_INVALID);
    }
    if value.is_infinite() {
        return Err(PARSE_OVERFLOW);
    }
    if value == 0.0 && significand_is_nonzero(bytes) {
        return Err(PARSE_UNDERFLOW);
    }
    Ok(value.to_bits())
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__parse_f32(input: RtString, bits_out: *mut u32) -> u8 {
    if bits_out.is_null() {
        return PARSE_INVALID;
    }
    let Some(parsed) = with_input_bytes(input, parse_f32_bits) else {
        return PARSE_INVALID;
    };
    match parsed {
        Ok(bits) => {
            unsafe { bits_out.write(bits) };
            PARSE_OK
        }
        Err(status) => status,
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__parse_f64(input: RtString, bits_out: *mut u64) -> u8 {
    if bits_out.is_null() {
        return PARSE_INVALID;
    }
    let Some(parsed) = with_input_bytes(input, parse_f64_bits) else {
        return PARSE_INVALID;
    };
    match parsed {
        Ok(bits) => {
            unsafe { bits_out.write(bits) };
            PARSE_OK
        }
        Err(status) => status,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rt_string(value: &str) -> RtString {
        RtString {
            ptr: value.as_ptr(),
            len: value.len(),
        }
    }

    #[test]
    fn parses_correctly_rounded_f32_bits() {
        let mut bits = 0_u32;
        assert_eq!(__rt__parse_f32(rt_string("0.1"), &mut bits), PARSE_OK);
        assert_eq!(f32::from_bits(bits), 0.1_f32);
    }

    #[test]
    fn classifies_f32_range_and_input_failures() {
        let mut bits = 0_u32;
        assert_eq!(
            __rt__parse_f32(rt_string("3.5e38"), &mut bits),
            PARSE_OVERFLOW
        );
        assert_eq!(
            __rt__parse_f32(rt_string("1e-100"), &mut bits),
            PARSE_UNDERFLOW
        );
        assert_eq!(__rt__parse_f32(rt_string("0e-999"), &mut bits), PARSE_OK);
        assert_eq!(f32::from_bits(bits), 0.0);
        assert_eq!(
            __rt__parse_f32(rt_string("not-a-float"), &mut bits),
            PARSE_INVALID
        );
        assert_eq!(__rt__parse_f32(rt_string("NaN"), &mut bits), PARSE_INVALID);
    }

    #[test]
    fn parses_and_classifies_f64_values() {
        let mut bits = 0_u64;
        assert_eq!(__rt__parse_f64(rt_string("-1.25e3"), &mut bits), PARSE_OK);
        assert_eq!(f64::from_bits(bits), -1250.0_f64);
        assert_eq!(
            __rt__parse_f64(rt_string("1e309"), &mut bits),
            PARSE_OVERFLOW
        );
        assert_eq!(
            __rt__parse_f64(rt_string("1e-400"), &mut bits),
            PARSE_UNDERFLOW
        );
    }
}
