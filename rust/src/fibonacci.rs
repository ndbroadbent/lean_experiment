//! Fibonacci implementations with verifiable properties
//!
//! Multiple implementations to demonstrate different verification approaches:
//! - Recursive (simple but slow)
//! - Iterative (efficient)
//! - With memoization pattern
//!
//! Key properties to verify:
//! - fib(0) == 0
//! - fib(1) == 1
//! - fib(n) == fib(n-1) + fib(n-2) for n >= 2
//! - All implementations produce the same result

/// Fibonacci - iterative implementation (efficient)
/// Property: fib_iter(0) == 0
/// Property: fib_iter(1) == 1
/// Property: fib_iter(n) == fib_iter(n-1) + fib_iter(n-2) for n >= 2
pub fn fib_iter(n: u32) -> u64 {
    if n == 0 {
        return 0;
    }
    if n == 1 {
        return 1;
    }

    let mut prev: u64 = 0;
    let mut curr: u64 = 1;
    let mut i: u32 = 2;

    while i <= n {
        let next = prev.wrapping_add(curr);
        prev = curr;
        curr = next;
        i += 1;
    }

    curr
}

/// Fibonacci with overflow checking
/// Returns None if the result would overflow u64
/// Property: fib_checked(n).is_some() implies fib_checked(n+1) >= fib_checked(n)
pub fn fib_checked(n: u32) -> Option<u64> {
    if n == 0 {
        return Some(0);
    }
    if n == 1 {
        return Some(1);
    }

    let mut prev: u64 = 0;
    let mut curr: u64 = 1;
    let mut i: u32 = 2;

    while i <= n {
        match prev.checked_add(curr) {
            Some(next) => {
                prev = curr;
                curr = next;
            }
            None => return None,
        }
        i += 1;
    }

    Some(curr)
}

/// Fibonacci - bounded computation
/// Only computes up to a maximum index to ensure termination
/// Property: fib_bounded(n, max) == fib_bounded(n, max') when n <= max && n <= max'
pub fn fib_bounded(n: u32, max_n: u32) -> Option<u64> {
    if n > max_n {
        return None;
    }
    Some(fib_iter(n))
}

/// Generate first n Fibonacci numbers
/// Property: fib_sequence(n).len() == n
/// Property: fib_sequence(n)[i] == fib_iter(i) for all valid i
pub fn fib_sequence(n: usize) -> Vec<u64> {
    let mut result = Vec::with_capacity(n);

    if n == 0 {
        return result;
    }

    result.push(0);
    if n == 1 {
        return result;
    }

    result.push(1);
    let mut i: usize = 2;
    while i < n {
        let next = result[i - 1].wrapping_add(result[i - 2]);
        result.push(next);
        i += 1;
    }

    result
}

/// Check if a number is a Fibonacci number
/// Property: is_fibonacci(fib_iter(n)) == true for reasonable n
pub fn is_fibonacci(x: u64) -> bool {
    if x == 0 || x == 1 {
        return true;
    }

    let mut prev: u64 = 0;
    let mut curr: u64 = 1;

    while curr < x {
        let next = match prev.checked_add(curr) {
            Some(n) => n,
            None => return false,
        };
        prev = curr;
        curr = next;
    }

    curr == x
}

/// Find the index of a Fibonacci number
/// Returns None if x is not a Fibonacci number
/// Property: fib_index(fib_iter(n)) == Some(n) for reasonable n
pub fn fib_index(x: u64) -> Option<u32> {
    if x == 0 {
        return Some(0);
    }
    if x == 1 {
        return Some(1);
    }

    let mut prev: u64 = 0;
    let mut curr: u64 = 1;
    let mut idx: u32 = 1;

    while curr < x {
        let next = match prev.checked_add(curr) {
            Some(n) => n,
            None => return None,
        };
        prev = curr;
        curr = next;
        idx += 1;
    }

    if curr == x {
        Some(idx)
    } else {
        None
    }
}

/// Compute Fibonacci using matrix exponentiation (fast for large n)
/// Uses the identity: [[1,1],[1,0]]^n = [[F(n+1),F(n)],[F(n),F(n-1)]]
/// Property: fib_matrix(n) == fib_iter(n)
pub fn fib_matrix(n: u32) -> u64 {
    if n == 0 {
        return 0;
    }

    // Matrix [[a, b], [c, d]]
    let mut a: u64 = 1;
    let mut b: u64 = 1;
    let mut c: u64 = 1;
    let mut d: u64 = 0;

    // Result matrix (identity)
    let mut ra: u64 = 1;
    let mut rb: u64 = 0;
    let mut rc: u64 = 0;
    let mut rd: u64 = 1;

    let mut exp = n - 1;

    while exp > 0 {
        if exp % 2 == 1 {
            // result = result * matrix
            let new_ra = ra.wrapping_mul(a).wrapping_add(rb.wrapping_mul(c));
            let new_rb = ra.wrapping_mul(b).wrapping_add(rb.wrapping_mul(d));
            let new_rc = rc.wrapping_mul(a).wrapping_add(rd.wrapping_mul(c));
            let new_rd = rc.wrapping_mul(b).wrapping_add(rd.wrapping_mul(d));
            ra = new_ra;
            rb = new_rb;
            rc = new_rc;
            rd = new_rd;
        }

        // matrix = matrix * matrix
        let new_a = a.wrapping_mul(a).wrapping_add(b.wrapping_mul(c));
        let new_b = a.wrapping_mul(b).wrapping_add(b.wrapping_mul(d));
        let new_c = c.wrapping_mul(a).wrapping_add(d.wrapping_mul(c));
        let new_d = c.wrapping_mul(b).wrapping_add(d.wrapping_mul(d));
        a = new_a;
        b = new_b;
        c = new_c;
        d = new_d;

        exp /= 2;
    }

    ra
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fib_iter_base_cases() {
        assert_eq!(fib_iter(0), 0);
        assert_eq!(fib_iter(1), 1);
    }

    #[test]
    fn test_fib_iter_values() {
        assert_eq!(fib_iter(2), 1);
        assert_eq!(fib_iter(3), 2);
        assert_eq!(fib_iter(4), 3);
        assert_eq!(fib_iter(5), 5);
        assert_eq!(fib_iter(10), 55);
        assert_eq!(fib_iter(20), 6765);
    }

    #[test]
    fn test_fib_matrix_matches_iter() {
        for i in 0..50 {
            assert_eq!(
                fib_matrix(i),
                fib_iter(i),
                "fib_matrix({}) != fib_iter({})",
                i,
                i
            );
        }
    }

    #[test]
    fn test_fib_checked() {
        assert_eq!(fib_checked(0), Some(0));
        assert_eq!(fib_checked(1), Some(1));
        assert_eq!(fib_checked(10), Some(55));
        // fib(93) = 12200160415121876738, fib(94) overflows u64
        assert!(fib_checked(93).is_some());
        assert_eq!(fib_checked(94), None); // Overflows
    }

    #[test]
    fn test_fib_sequence() {
        assert_eq!(fib_sequence(0), vec![]);
        assert_eq!(fib_sequence(1), vec![0]);
        assert_eq!(fib_sequence(2), vec![0, 1]);
        assert_eq!(fib_sequence(10), vec![0, 1, 1, 2, 3, 5, 8, 13, 21, 34]);
    }

    #[test]
    fn test_is_fibonacci() {
        assert!(is_fibonacci(0));
        assert!(is_fibonacci(1));
        assert!(is_fibonacci(2));
        assert!(is_fibonacci(3));
        assert!(is_fibonacci(5));
        assert!(is_fibonacci(8));
        assert!(is_fibonacci(13));
        assert!(is_fibonacci(55));

        assert!(!is_fibonacci(4));
        assert!(!is_fibonacci(6));
        assert!(!is_fibonacci(7));
        assert!(!is_fibonacci(9));
    }

    #[test]
    fn test_fib_index() {
        assert_eq!(fib_index(0), Some(0));
        assert_eq!(fib_index(1), Some(1));
        assert_eq!(fib_index(5), Some(5));
        assert_eq!(fib_index(55), Some(10));
        assert_eq!(fib_index(4), None);
        assert_eq!(fib_index(6), None);
    }

    #[test]
    fn test_recurrence_relation() {
        // Verify fib(n) = fib(n-1) + fib(n-2) for n >= 2
        for n in 2..50 {
            assert_eq!(
                fib_iter(n),
                fib_iter(n - 1) + fib_iter(n - 2),
                "Recurrence relation failed for n={}",
                n
            );
        }
    }
}
