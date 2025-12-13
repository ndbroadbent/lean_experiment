//! String operations with verifiable properties
//!
//! Note: Aeneas has limited String support, so we use &str and
//! simple byte-level operations where possible.

/// Concatenate two strings
/// Property: concat("", s) == s
/// Property: concat(s, "") == s
pub fn concat(a: &str, b: &str) -> String {
    let mut result = String::from(a);
    result.push_str(b);
    result
}

/// Check if string is empty
/// Property: is_empty("") == true
/// Property: is_empty(s) == (length(s) == 0)
pub fn is_empty(s: &str) -> bool {
    s.is_empty()
}

/// Get string length in bytes
pub fn length(s: &str) -> usize {
    s.len()
}

/// Check if string starts with prefix
/// Property: starts_with(s, "") == true
/// Property: starts_with("hello", "he") == true
pub fn starts_with(s: &str, prefix: &str) -> bool {
    s.starts_with(prefix)
}

/// Check if string ends with suffix
/// Property: ends_with(s, "") == true
pub fn ends_with(s: &str, suffix: &str) -> bool {
    s.ends_with(suffix)
}

/// Check if two strings are equal
/// Property: equals(s, s) == true (reflexivity)
/// Property: equals(a, b) == equals(b, a) (symmetry)
pub fn equals(a: &str, b: &str) -> bool {
    a == b
}

/// Validate input length (max 10 chars) and process
/// If input is "hello", append " world"
/// Otherwise, prepend "You typed: "
/// Property: validate_and_process with len > 10 returns None
pub fn validate_and_process(input: &str) -> Option<String> {
    if input.len() > 10 {
        return None;
    }

    if input == "hello" {
        Some(concat(input, " world"))
    } else {
        Some(concat("You typed: ", input))
    }
}

/// Reverse a string (byte-wise, ASCII only)
/// Property: reverse(reverse(s)) == s for ASCII
pub fn reverse_ascii(s: &str) -> String {
    s.chars().rev().collect()
}

/// Count occurrences of a character
pub fn count_char(s: &str, c: char) -> usize {
    s.chars().filter(|&ch| ch == c).count()
}

/// Check if string contains only ASCII digits
/// Property: is_numeric("123") == true
/// Property: is_numeric("12a") == false
/// Property: is_numeric("") == true (vacuous truth)
pub fn is_numeric(s: &str) -> bool {
    s.chars().all(|c| c.is_ascii_digit())
}

/// Check if string contains only ASCII alphabetic chars
pub fn is_alphabetic(s: &str) -> bool {
    s.chars().all(|c| c.is_ascii_alphabetic())
}

/// Convert to uppercase (ASCII only)
pub fn to_uppercase(s: &str) -> String {
    s.to_ascii_uppercase()
}

/// Convert to lowercase (ASCII only)
pub fn to_lowercase(s: &str) -> String {
    s.to_ascii_lowercase()
}

/// Trim leading and trailing whitespace
pub fn trim(s: &str) -> &str {
    s.trim()
}

/// Safe substring extraction
/// Returns None if indices are out of bounds
pub fn substring(s: &str, start: usize, end: usize) -> Option<&str> {
    if start > end || end > s.len() {
        None
    } else {
        Some(&s[start..end])
    }
}

/// Check if string is a palindrome (ASCII, case-insensitive)
/// Property: is_palindrome("racecar") == true
/// Property: is_palindrome("") == true
/// Property: is_palindrome("a") == true
pub fn is_palindrome(s: &str) -> bool {
    let chars: Vec<char> = s.chars().map(|c| c.to_ascii_lowercase()).collect();
    let len = chars.len();

    let mut i = 0;
    while i < len / 2 {
        if chars[i] != chars[len - 1 - i] {
            return false;
        }
        i += 1;
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_concat() {
        assert_eq!(concat("hello", " world"), "hello world");
        assert_eq!(concat("", "test"), "test");
        assert_eq!(concat("test", ""), "test");
    }

    #[test]
    fn test_validate_and_process() {
        assert_eq!(
            validate_and_process("hello"),
            Some("hello world".to_string())
        );
        assert_eq!(
            validate_and_process("hi"),
            Some("You typed: hi".to_string())
        );
        assert_eq!(validate_and_process("this is way too long"), None);
    }

    #[test]
    fn test_is_palindrome() {
        assert!(is_palindrome("racecar"));
        assert!(is_palindrome("RaceCar"));
        assert!(is_palindrome(""));
        assert!(is_palindrome("a"));
        assert!(!is_palindrome("hello"));
    }

    #[test]
    fn test_reverse() {
        assert_eq!(reverse_ascii("hello"), "olleh");
        assert_eq!(reverse_ascii(""), "");
        assert_eq!(reverse_ascii("a"), "a");
    }

    #[test]
    fn test_substring() {
        assert_eq!(substring("hello", 0, 2), Some("he"));
        assert_eq!(substring("hello", 0, 5), Some("hello"));
        assert_eq!(substring("hello", 3, 2), None); // invalid range
        assert_eq!(substring("hello", 0, 10), None); // out of bounds
    }
}
