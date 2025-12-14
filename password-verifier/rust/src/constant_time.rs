//! Constant-time comparison functions
//!
//! These functions are designed to prevent timing attacks by ensuring
//! the same operations are performed regardless of input values.
//!
//! Key property: NO EARLY EXIT - we always examine all bytes.

/// Constant-time byte comparison using XOR accumulation.
///
/// Returns true if all bytes are equal, false otherwise.
/// CRITICAL: Always iterates through all bytes - no early exit.
///
/// The algorithm:
/// 1. XOR each pair of bytes: equal bytes produce 0, different bytes produce non-zero
/// 2. OR all XOR results together: if any difference exists, result is non-zero
/// 3. Return true only if accumulated result is 0
pub fn ct_eq_bytes(a: &[u8; 8], b: &[u8; 8]) -> bool {
    let mut acc: u8 = 0;

    // Unrolled loop - always executes exactly 8 iterations
    acc |= a[0] ^ b[0];
    acc |= a[1] ^ b[1];
    acc |= a[2] ^ b[2];
    acc |= a[3] ^ b[3];
    acc |= a[4] ^ b[4];
    acc |= a[5] ^ b[5];
    acc |= a[6] ^ b[6];
    acc |= a[7] ^ b[7];

    acc == 0
}

/// Constant-time comparison for 16-byte arrays (e.g., 128-bit values)
pub fn ct_eq_16(a: &[u8; 16], b: &[u8; 16]) -> bool {
    let mut acc: u8 = 0;

    acc |= a[0] ^ b[0];
    acc |= a[1] ^ b[1];
    acc |= a[2] ^ b[2];
    acc |= a[3] ^ b[3];
    acc |= a[4] ^ b[4];
    acc |= a[5] ^ b[5];
    acc |= a[6] ^ b[6];
    acc |= a[7] ^ b[7];
    acc |= a[8] ^ b[8];
    acc |= a[9] ^ b[9];
    acc |= a[10] ^ b[10];
    acc |= a[11] ^ b[11];
    acc |= a[12] ^ b[12];
    acc |= a[13] ^ b[13];
    acc |= a[14] ^ b[14];
    acc |= a[15] ^ b[15];

    acc == 0
}

/// Constant-time comparison for 32-byte arrays (e.g., SHA-256 hash)
pub fn ct_eq_32(a: &[u8; 32], b: &[u8; 32]) -> bool {
    let mut acc: u8 = 0;

    // First 16 bytes
    acc |= a[0] ^ b[0];
    acc |= a[1] ^ b[1];
    acc |= a[2] ^ b[2];
    acc |= a[3] ^ b[3];
    acc |= a[4] ^ b[4];
    acc |= a[5] ^ b[5];
    acc |= a[6] ^ b[6];
    acc |= a[7] ^ b[7];
    acc |= a[8] ^ b[8];
    acc |= a[9] ^ b[9];
    acc |= a[10] ^ b[10];
    acc |= a[11] ^ b[11];
    acc |= a[12] ^ b[12];
    acc |= a[13] ^ b[13];
    acc |= a[14] ^ b[14];
    acc |= a[15] ^ b[15];

    // Second 16 bytes
    acc |= a[16] ^ b[16];
    acc |= a[17] ^ b[17];
    acc |= a[18] ^ b[18];
    acc |= a[19] ^ b[19];
    acc |= a[20] ^ b[20];
    acc |= a[21] ^ b[21];
    acc |= a[22] ^ b[22];
    acc |= a[23] ^ b[23];
    acc |= a[24] ^ b[24];
    acc |= a[25] ^ b[25];
    acc |= a[26] ^ b[26];
    acc |= a[27] ^ b[27];
    acc |= a[28] ^ b[28];
    acc |= a[29] ^ b[29];
    acc |= a[30] ^ b[30];
    acc |= a[31] ^ b[31];

    acc == 0
}

/// XOR two bytes - exposed for proofs
pub fn xor_byte(a: u8, b: u8) -> u8 {
    a ^ b
}

/// OR two bytes - exposed for proofs
pub fn or_byte(a: u8, b: u8) -> u8 {
    a | b
}

/// Check if byte is zero - exposed for proofs
pub fn is_zero(x: u8) -> bool {
    x == 0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ct_eq_bytes_equal() {
        let a = [1, 2, 3, 4, 5, 6, 7, 8];
        let b = [1, 2, 3, 4, 5, 6, 7, 8];
        assert!(ct_eq_bytes(&a, &b));
    }

    #[test]
    fn test_ct_eq_bytes_different_first() {
        let a = [0, 2, 3, 4, 5, 6, 7, 8];
        let b = [1, 2, 3, 4, 5, 6, 7, 8];
        assert!(!ct_eq_bytes(&a, &b));
    }

    #[test]
    fn test_ct_eq_bytes_different_last() {
        let a = [1, 2, 3, 4, 5, 6, 7, 8];
        let b = [1, 2, 3, 4, 5, 6, 7, 9];
        assert!(!ct_eq_bytes(&a, &b));
    }

    #[test]
    fn test_ct_eq_bytes_different_middle() {
        let a = [1, 2, 3, 4, 5, 6, 7, 8];
        let b = [1, 2, 3, 99, 5, 6, 7, 8];
        assert!(!ct_eq_bytes(&a, &b));
    }

    #[test]
    fn test_ct_eq_bytes_all_zeros() {
        let a = [0, 0, 0, 0, 0, 0, 0, 0];
        let b = [0, 0, 0, 0, 0, 0, 0, 0];
        assert!(ct_eq_bytes(&a, &b));
    }

    #[test]
    fn test_ct_eq_bytes_all_ones() {
        let a = [255, 255, 255, 255, 255, 255, 255, 255];
        let b = [255, 255, 255, 255, 255, 255, 255, 255];
        assert!(ct_eq_bytes(&a, &b));
    }

    #[test]
    fn test_ct_eq_16() {
        let a = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
        let b = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
        assert!(ct_eq_16(&a, &b));

        let c = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99];
        assert!(!ct_eq_16(&a, &c));
    }

    #[test]
    fn test_ct_eq_32() {
        let a = [0u8; 32];
        let b = [0u8; 32];
        assert!(ct_eq_32(&a, &b));

        let mut c = [0u8; 32];
        c[31] = 1;
        assert!(!ct_eq_32(&a, &c));
    }

    #[test]
    fn test_xor_properties() {
        // XOR with self is 0
        assert_eq!(xor_byte(42, 42), 0);
        // XOR with 0 is identity
        assert_eq!(xor_byte(42, 0), 42);
        // XOR is commutative
        assert_eq!(xor_byte(10, 20), xor_byte(20, 10));
    }
}
