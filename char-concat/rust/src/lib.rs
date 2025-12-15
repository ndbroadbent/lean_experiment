//! Character concatenation as pure arithmetic
//!
//! Strings are just integers viewed as sequences of character codes.
//! This module proves that string operations are bit manipulation.
//!
//! Key insight: a ⊕ b = (a << 8) | b = a × 256 + b
//!
//! Properties to prove:
//! 1. first_char(concat_chars(a, b)) = a
//! 2. second_char(concat_chars(a, b)) = b
//! 3. concat_chars is injective: concat_chars(a,b) = concat_chars(c,d) → a=c ∧ b=d

/// Concatenate two ASCII bytes into a u16 "string"
///
/// Mathematical definition: a ⊕ b = (a << 8) | b = a × 256 + b
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

/// Roundtrip: reconstruct the original u16 from its components
///
/// Property: concat_chars(first_char(s), second_char(s)) = s
pub fn roundtrip(s: u16) -> u16 {
    concat_chars(first_char(s), second_char(s))
}

/// Check equality of two 2-char strings
pub fn chars_equal(s1: u16, s2: u16) -> bool {
    s1 == s2
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_concat_chars() {
        // 'a' = 97, 'b' = 98
        assert_eq!(concat_chars(97, 98), 0x6162);
        assert_eq!(concat_chars(97, 97), 0x6161);
    }

    #[test]
    fn test_first_char_roundtrip() {
        for a in 0..=255u8 {
            for b in 0..=255u8 {
                let s = concat_chars(a, b);
                assert_eq!(first_char(s), a);
            }
        }
    }

    #[test]
    fn test_second_char_roundtrip() {
        for a in 0..=255u8 {
            for b in 0..=255u8 {
                let s = concat_chars(a, b);
                assert_eq!(second_char(s), b);
            }
        }
    }

    #[test]
    fn test_full_roundtrip() {
        for s in 0..=u16::MAX {
            assert_eq!(roundtrip(s), s);
        }
    }
}
