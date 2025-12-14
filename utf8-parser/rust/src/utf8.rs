//! UTF-8 parsing as pure operations on byte vectors
//!
//! This module implements UTF-8 parsing without using Rust's String type.
//! All functions operate on &[u8] or fixed arrays, making them verifiable via Aeneas.
//!
//! UTF-8 encoding:
//! - 0xxxxxxx              → 1-byte (ASCII, 0x00-0x7F)
//! - 110xxxxx 10xxxxxx     → 2-byte (0xC0-0xDF, then 0x80-0xBF)
//! - 1110xxxx 10xxxxxx × 2 → 3-byte (0xE0-0xEF, then 0x80-0xBF × 2)
//! - 11110xxx 10xxxxxx × 3 → 4-byte (0xF0-0xF7, then 0x80-0xBF × 3)

/// Determine the length of a UTF-8 sequence from its first byte.
/// Returns 0 for invalid leading bytes.
pub fn sequence_length(first_byte: u8) -> u8 {
    if first_byte & 0x80 == 0x00 {
        1 // 0xxxxxxx - ASCII
    } else if first_byte & 0xE0 == 0xC0 {
        2 // 110xxxxx
    } else if first_byte & 0xF0 == 0xE0 {
        3 // 1110xxxx
    } else if first_byte & 0xF8 == 0xF0 {
        4 // 11110xxx
    } else {
        0 // Invalid (continuation byte or invalid pattern)
    }
}

/// Check if a byte is a valid UTF-8 continuation byte (10xxxxxx).
pub fn is_continuation(byte: u8) -> bool {
    byte & 0xC0 == 0x80
}

/// Check if a byte is a valid UTF-8 leading byte.
pub fn is_leading(byte: u8) -> bool {
    sequence_length(byte) > 0
}

/// Validate a 1-byte UTF-8 sequence (ASCII).
pub fn validate_1byte(b0: u8) -> bool {
    sequence_length(b0) == 1
}

/// Validate a 2-byte UTF-8 sequence.
pub fn validate_2byte(b0: u8, b1: u8) -> bool {
    sequence_length(b0) == 2 && is_continuation(b1)
}

/// Validate a 3-byte UTF-8 sequence.
pub fn validate_3byte(b0: u8, b1: u8, b2: u8) -> bool {
    sequence_length(b0) == 3 && is_continuation(b1) && is_continuation(b2)
}

/// Validate a 4-byte UTF-8 sequence.
pub fn validate_4byte(b0: u8, b1: u8, b2: u8, b3: u8) -> bool {
    sequence_length(b0) == 4
        && is_continuation(b1)
        && is_continuation(b2)
        && is_continuation(b3)
}

/// A parsed code point stored in a fixed 4-byte array.
/// This is our "inner vector" in the vector-of-vectors model.
/// - bytes[0..len] contain the valid UTF-8 bytes
/// - bytes[len..4] are padding zeros
pub struct CodePoint {
    pub bytes: [u8; 4],
    pub len: u8,
}

/// Create a 1-byte code point (ASCII).
pub fn code_point_1(b0: u8) -> CodePoint {
    CodePoint {
        bytes: [b0, 0, 0, 0],
        len: 1,
    }
}

/// Create a 2-byte code point.
pub fn code_point_2(b0: u8, b1: u8) -> CodePoint {
    CodePoint {
        bytes: [b0, b1, 0, 0],
        len: 2,
    }
}

/// Create a 3-byte code point.
pub fn code_point_3(b0: u8, b1: u8, b2: u8) -> CodePoint {
    CodePoint {
        bytes: [b0, b1, b2, 0],
        len: 3,
    }
}

/// Create a 4-byte code point.
pub fn code_point_4(b0: u8, b1: u8, b2: u8, b3: u8) -> CodePoint {
    CodePoint {
        bytes: [b0, b1, b2, b3],
        len: 4,
    }
}

/// Get the first byte of a code point.
pub fn code_point_byte0(cp: &CodePoint) -> u8 {
    cp.bytes[0]
}

/// Get the second byte of a code point (0 if len < 2).
pub fn code_point_byte1(cp: &CodePoint) -> u8 {
    cp.bytes[1]
}

/// Get the third byte of a code point (0 if len < 3).
pub fn code_point_byte2(cp: &CodePoint) -> u8 {
    cp.bytes[2]
}

/// Get the fourth byte of a code point (0 if len < 4).
pub fn code_point_byte3(cp: &CodePoint) -> u8 {
    cp.bytes[3]
}

/// Check if two code points are equal.
pub fn code_point_eq(a: &CodePoint, b: &CodePoint) -> bool {
    a.len == b.len
        && a.bytes[0] == b.bytes[0]
        && a.bytes[1] == b.bytes[1]
        && a.bytes[2] == b.bytes[2]
        && a.bytes[3] == b.bytes[3]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sequence_length() {
        // ASCII
        assert_eq!(sequence_length(0x00), 1);
        assert_eq!(sequence_length(0x7F), 1);
        assert_eq!(sequence_length(b'a'), 1);

        // 2-byte
        assert_eq!(sequence_length(0xC2), 2);
        assert_eq!(sequence_length(0xDF), 2);

        // 3-byte
        assert_eq!(sequence_length(0xE0), 3);
        assert_eq!(sequence_length(0xEF), 3);

        // 4-byte
        assert_eq!(sequence_length(0xF0), 4);
        assert_eq!(sequence_length(0xF4), 4);

        // Invalid (continuation bytes)
        assert_eq!(sequence_length(0x80), 0);
        assert_eq!(sequence_length(0xBF), 0);

        // Invalid (too high)
        assert_eq!(sequence_length(0xF8), 0);
        assert_eq!(sequence_length(0xFF), 0);
    }

    #[test]
    fn test_is_continuation() {
        assert!(is_continuation(0x80));
        assert!(is_continuation(0xBF));
        assert!(!is_continuation(0x00));
        assert!(!is_continuation(0x7F));
        assert!(!is_continuation(0xC0));
    }

    #[test]
    fn test_validate_sequences() {
        // 1-byte (ASCII)
        assert!(validate_1byte(b'a'));
        assert!(!validate_1byte(0xC0));

        // 2-byte: é = [0xC3, 0xA9]
        assert!(validate_2byte(0xC3, 0xA9));
        assert!(!validate_2byte(0xC3, 0x00)); // Bad continuation

        // 3-byte: € = [0xE2, 0x82, 0xAC]
        assert!(validate_3byte(0xE2, 0x82, 0xAC));

        // 4-byte: 😀 = [0xF0, 0x9F, 0x98, 0x80]
        assert!(validate_4byte(0xF0, 0x9F, 0x98, 0x80));
    }

    #[test]
    fn test_code_point_constructors() {
        let cp1 = code_point_1(b'a');
        assert_eq!(cp1.len, 1);
        assert_eq!(cp1.bytes, [b'a', 0, 0, 0]);

        let cp2 = code_point_2(0xC3, 0xA9);
        assert_eq!(cp2.len, 2);
        assert_eq!(cp2.bytes, [0xC3, 0xA9, 0, 0]);

        let cp4 = code_point_4(0xF0, 0x9F, 0x98, 0x80);
        assert_eq!(cp4.len, 4);
        assert_eq!(cp4.bytes, [0xF0, 0x9F, 0x98, 0x80]);
    }

    #[test]
    fn test_code_point_eq() {
        let a = code_point_1(b'a');
        let b = code_point_1(b'a');
        let c = code_point_1(b'b');

        assert!(code_point_eq(&a, &b));
        assert!(!code_point_eq(&a, &c));

        let e1 = code_point_2(0xC3, 0xA9);
        let e2 = code_point_2(0xC3, 0xA9);
        assert!(code_point_eq(&e1, &e2));
    }
}
