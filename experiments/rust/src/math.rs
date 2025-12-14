//! Mathematical operations with verifiable properties

/// Addition - the simplest operation
/// Property: add(a, b) == add(b, a) (commutativity)
pub fn add(a: u32, b: u32) -> u32 {
    a.wrapping_add(b)
}

/// Multiplication
/// Property: mul(a, 1) == a (identity)
/// Property: mul(a, b) == mul(b, a) (commutativity)
pub fn mul(a: u32, b: u32) -> u32 {
    a.wrapping_mul(b)
}

/// Safe division - returns None on divide by zero
/// Property: div(a, b).is_some() implies b != 0
/// Property: div(a, 1) == Some(a)
pub fn div(a: u32, b: u32) -> Option<u32> {
    if b == 0 {
        None
    } else {
        Some(a / b)
    }
}

/// Modulo operation - returns None on mod by zero
pub fn modulo(a: u32, b: u32) -> Option<u32> {
    if b == 0 {
        None
    } else {
        Some(a % b)
    }
}

/// Greatest common divisor using Euclidean algorithm
/// Property: gcd(a, b) == gcd(b, a)
/// Property: gcd(a, 0) == a
/// Property: gcd(a, a) == a
pub fn gcd(mut a: u32, mut b: u32) -> u32 {
    while b != 0 {
        let temp = b;
        b = a % b;
        a = temp;
    }
    a
}

/// Least common multiple
/// Property: lcm(a, b) >= max(a, b) when both > 0
pub fn lcm(a: u32, b: u32) -> Option<u32> {
    if a == 0 || b == 0 {
        Some(0)
    } else {
        let g = gcd(a, b);
        // Avoid overflow by dividing first
        Some((a / g).wrapping_mul(b))
    }
}

/// Power function (exponentiation by squaring)
/// Property: pow(a, 0) == 1
/// Property: pow(a, 1) == a
pub fn pow(base: u32, exp: u32) -> u32 {
    let mut result: u32 = 1;
    let mut base = base;
    let mut exp = exp;

    while exp > 0 {
        if exp % 2 == 1 {
            result = result.wrapping_mul(base);
        }
        exp /= 2;
        base = base.wrapping_mul(base);
    }
    result
}

/// Check if a number is even
/// Property: is_even(n) == !is_odd(n)
pub fn is_even(n: u32) -> bool {
    n % 2 == 0
}

/// Check if a number is odd
pub fn is_odd(n: u32) -> bool {
    n % 2 == 1
}

/// Absolute difference (always positive)
/// Property: abs_diff(a, b) == abs_diff(b, a)
pub fn abs_diff(a: u32, b: u32) -> u32 {
    if a > b {
        a - b
    } else {
        b - a
    }
}

/// Factorial (iterative, with overflow protection)
/// Property: factorial(0) == 1
/// Property: factorial(1) == 1
pub fn factorial(n: u32) -> Option<u32> {
    // Factorial grows very fast; 13! overflows u32
    if n > 12 {
        return None;
    }

    let mut result: u32 = 1;
    let mut i: u32 = 2;
    while i <= n {
        result = result.wrapping_mul(i);
        i += 1;
    }
    Some(result)
}

/// Check if prime (simple trial division)
/// Property: is_prime(2) == true
/// Property: is_prime(1) == false
/// Property: is_prime(0) == false
pub fn is_prime(n: u32) -> bool {
    if n < 2 {
        return false;
    }
    if n == 2 {
        return true;
    }
    if n % 2 == 0 {
        return false;
    }

    let mut i: u32 = 3;
    while i.wrapping_mul(i) <= n {
        if n % i == 0 {
            return false;
        }
        i += 2;
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add_commutative() {
        assert_eq!(add(3, 5), add(5, 3));
        assert_eq!(add(0, 10), add(10, 0));
    }

    #[test]
    fn test_gcd() {
        assert_eq!(gcd(48, 18), 6);
        assert_eq!(gcd(17, 13), 1);
        assert_eq!(gcd(100, 0), 100);
        assert_eq!(gcd(0, 100), 100);
    }

    #[test]
    fn test_factorial() {
        assert_eq!(factorial(0), Some(1));
        assert_eq!(factorial(1), Some(1));
        assert_eq!(factorial(5), Some(120));
        assert_eq!(factorial(12), Some(479001600));
        assert_eq!(factorial(13), None); // overflow
    }

    #[test]
    fn test_is_prime() {
        assert!(!is_prime(0));
        assert!(!is_prime(1));
        assert!(is_prime(2));
        assert!(is_prime(3));
        assert!(!is_prime(4));
        assert!(is_prime(17));
        assert!(!is_prime(18));
    }

    #[test]
    fn test_pow() {
        assert_eq!(pow(2, 0), 1);
        assert_eq!(pow(2, 1), 2);
        assert_eq!(pow(2, 10), 1024);
        assert_eq!(pow(3, 4), 81);
    }
}
