//! Simple functions for Aeneas verification
//! Minimal subset to test the toolchain

/// Add two numbers
pub fn add(a: u32, b: u32) -> u32 {
    a + b
}

/// Multiply two numbers
pub fn mul(a: u32, b: u32) -> u32 {
    a * b
}

/// GCD using Euclidean algorithm
/// Property: gcd(a, 0) == a
/// Property: gcd(a, b) == gcd(b, a % b)
pub fn gcd(a: u32, b: u32) -> u32 {
    if b == 0 {
        a
    } else {
        gcd(b, a % b)
    }
}

/// Factorial
/// Property: factorial(0) == 1
/// Property: factorial(n) == n * factorial(n-1)
pub fn factorial(n: u32) -> u32 {
    if n == 0 {
        1
    } else {
        n * factorial(n - 1)
    }
}

/// Power function
pub fn pow(base: u32, exp: u32) -> u32 {
    if exp == 0 {
        1
    } else {
        base * pow(base, exp - 1)
    }
}

/// Check if a number is even
pub fn is_even(n: u32) -> bool {
    n % 2 == 0
}

/// Absolute difference
pub fn abs_diff(a: u32, b: u32) -> u32 {
    if a > b {
        a - b
    } else {
        b - a
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add() {
        assert_eq!(add(2, 3), 5);
    }

    #[test]
    fn test_gcd() {
        assert_eq!(gcd(48, 18), 6);
        assert_eq!(gcd(10, 0), 10);
    }

    #[test]
    fn test_factorial() {
        assert_eq!(factorial(0), 1);
        assert_eq!(factorial(5), 120);
    }
}
