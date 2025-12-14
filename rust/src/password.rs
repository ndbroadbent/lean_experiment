//! Password-protected secret revelation
//!
//! This module demonstrates a formally verified password checker.
//! The secret is only revealed when the correct password is provided.
//!
//! Security properties to prove:
//! 1. Correct password → secret is revealed
//! 2. Wrong password → secret is NOT revealed
//! 3. Comparison is constant-time (no timing attack)

use crate::constant_time::ct_eq_bytes;

/// The secret that will be revealed on correct password.
/// In a real application, this would be loaded from secure storage.
/// For verification purposes, we use a constant.
pub const SECRET: [u8; 8] = [84, 104, 101, 32, 107, 101, 121, 33]; // "The key!"

/// The password hash (in reality, use proper hashing like Argon2).
/// For this POC, we store the password directly for simplicity.
/// Password: "hunter42" (truncated/padded to 8 bytes)
pub const PASSWORD: [u8; 8] = [104, 117, 110, 116, 101, 114, 52, 50]; // "hunter42"

/// Check if the provided password matches the stored password.
/// Uses constant-time comparison to prevent timing attacks.
pub fn check_password(input: &[u8; 8]) -> bool {
    ct_eq_bytes(input, &PASSWORD)
}

/// Attempt to reveal the secret with the given password.
/// Returns Some(secret) if password is correct, None otherwise.
///
/// This is the core function we want to verify:
/// - ∀ input. input = PASSWORD → reveal_secret(input) = Some(SECRET)
/// - ∀ input. input ≠ PASSWORD → reveal_secret(input) = None
pub fn reveal_secret(input: &[u8; 8]) -> Option<[u8; 8]> {
    if check_password(input) {
        Some(SECRET)
    } else {
        None
    }
}

/// Alternative formulation using Result for Aeneas compatibility.
/// Returns Ok(secret) on success, Err(()) on failure.
pub fn reveal_secret_result(input: &[u8; 8]) -> Result<[u8; 8], ()> {
    if check_password(input) {
        Ok(SECRET)
    } else {
        Err(())
    }
}

/// Get the secret bytes directly (for use in proofs).
pub fn get_secret() -> [u8; 8] {
    SECRET
}

/// Get the password bytes directly (for use in proofs).
pub fn get_password() -> [u8; 8] {
    PASSWORD
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_correct_password_reveals_secret() {
        let input = PASSWORD; // "hunter42"
        let result = reveal_secret(&input);
        assert_eq!(result, Some(SECRET));
    }

    #[test]
    fn test_wrong_password_reveals_nothing() {
        let wrong = [0, 0, 0, 0, 0, 0, 0, 0];
        let result = reveal_secret(&wrong);
        assert_eq!(result, None);
    }

    #[test]
    fn test_almost_correct_password_reveals_nothing() {
        // "hunter43" - off by one character
        let almost = [104, 117, 110, 116, 101, 114, 52, 51];
        let result = reveal_secret(&almost);
        assert_eq!(result, None);
    }

    #[test]
    fn test_check_password_correct() {
        assert!(check_password(&PASSWORD));
    }

    #[test]
    fn test_check_password_wrong() {
        let wrong = [1, 2, 3, 4, 5, 6, 7, 8];
        assert!(!check_password(&wrong));
    }

    #[test]
    fn test_secret_is_expected_value() {
        // "The key!" in ASCII
        assert_eq!(SECRET, [84, 104, 101, 32, 107, 101, 121, 33]);
    }

    #[test]
    fn test_password_is_expected_value() {
        // "hunter42" in ASCII
        assert_eq!(PASSWORD, [104, 117, 110, 116, 101, 114, 52, 50]);
    }
}
