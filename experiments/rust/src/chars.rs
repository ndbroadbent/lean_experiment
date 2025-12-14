//! Character operations as pure arithmetic
//!
//! Strings are just integers viewed as sequences of character codes.
//! This module provides the foundational operations for a formally
//! verified string library built on bit manipulation.

/// Concatenate two ASCII bytes into a u16 "string"
///
/// Mathematical definition: a ⊕ b = (a << 8) | b = a × 256 + b
///
/// Property: concat_chars('a', 'b') = 0x6162 = 24930
pub fn concat_chars(a: u8, b: u8) -> u16 {
    ((a as u16) << 8) | (b as u16)
}

/// Extract the first character from a 2-char u16 "string"
///
/// Property: first_char(concat_chars(a, b)) = a
pub fn first_char(s: u16) -> u8 {
    (s >> 8) as u8
}

/// Extract the second character from a 2-char u16 "string"
///
/// Property: second_char(concat_chars(a, b)) = b
pub fn second_char(s: u16) -> u8 {
    (s & 0xFF) as u8
}

/// Check if two 2-char strings are equal
///
/// This is just integer equality, but we make it explicit
pub fn chars_equal(s1: u16, s2: u16) -> bool {
    s1 == s2
}

/// Get the "length" of a u16 string (always 2 for non-zero, 0-2 depending on content)
///
/// For simplicity, we consider any u16 to represent exactly 2 characters
pub fn chars_len(_s: u16) -> u8 {
    2
}

// ============================================================================
// Array-based string representation
// ============================================================================

/// A string as an array of bytes (fixed size for now)
/// This is closer to how real strings work
pub fn array_concat(a: u8, b: u8) -> [u8; 2] {
    [a, b]
}

/// Get first element from array string
pub fn array_first(s: &[u8; 2]) -> u8 {
    s[0]
}

/// Get second element from array string
pub fn array_second(s: &[u8; 2]) -> u8 {
    s[1]
}

/// Check array string equality
pub fn array_equal(s1: &[u8; 2], s2: &[u8; 2]) -> bool {
    s1[0] == s2[0] && s1[1] == s2[1]
}

/// Get array length (always 2)
pub fn array_len(_s: &[u8; 2]) -> usize {
    2
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_concat_chars() {
        // 'a' = 97, 'b' = 98
        assert_eq!(concat_chars(97, 98), 0x6162);
        assert_eq!(concat_chars(97, 98), 24930);

        // 'a' = 97, 'a' = 97
        assert_eq!(concat_chars(97, 97), 0x6161);
        assert_eq!(concat_chars(97, 97), 24929);
    }

    #[test]
    fn test_first_char_roundtrip() {
        for a in 0..=255u8 {
            for b in 0..=255u8 {
                let s = concat_chars(a, b);
                assert_eq!(first_char(s), a, "first_char failed for a={}, b={}", a, b);
            }
        }
    }

    #[test]
    fn test_second_char_roundtrip() {
        for a in 0..=255u8 {
            for b in 0..=255u8 {
                let s = concat_chars(a, b);
                assert_eq!(second_char(s), b, "second_char failed for a={}, b={}", a, b);
            }
        }
    }

    #[test]
    fn test_equality_iff_components_equal() {
        // If concat_chars(a,b) = concat_chars(c,d), then a=c and b=d
        let s1 = concat_chars(97, 98);
        let s2 = concat_chars(97, 98);
        let s3 = concat_chars(98, 97);

        assert!(chars_equal(s1, s2));
        assert!(!chars_equal(s1, s3));
    }

    #[test]
    fn test_chars_len() {
        assert_eq!(chars_len(0), 2);
        assert_eq!(chars_len(24929), 2);
        assert_eq!(chars_len(0xFFFF), 2);
    }
}
