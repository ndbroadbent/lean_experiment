# PRD: Formally Verified Constant-Time Authentication

## Overview

Build a password authentication system in Rust where the critical security property—**constant-time comparison**—is formally proven in Lean via Aeneas.

## Problem Statement

### The Timing Attack

Traditional string comparison exits early on the first mismatch:

```rust
// VULNERABLE: Timing attack possible
fn compare(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() { return false; }
    for i in 0..a.len() {
        if a[i] != b[i] { return false; }  // ← EARLY EXIT leaks information
    }
    true
}
```

An attacker can measure response time:
- Password "AAAA" vs stored "SECRET" → fast rejection (fails on 'A' ≠ 'S')
- Password "SAAA" vs stored "SECRET" → slightly slower (fails on 'A' ≠ 'E')
- Password "SEAA" vs stored "SECRET" → even slower

By measuring timing, attackers can brute-force one character at a time: O(n×k) instead of O(k^n).

### The Solution: Constant-Time Comparison

```rust
// SECURE: No timing side-channel
fn constant_time_compare(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() { return false; }
    let mut result: u8 = 0;
    for i in 0..a.len() {
        result |= a[i] ^ b[i];  // ← NO EARLY EXIT, accumulates all differences
    }
    result == 0
}
```

This function:
1. Always examines ALL bytes
2. Takes the same time regardless of where mismatches occur
3. Reveals only "match" or "no match", not "how close"

### The Verification Challenge

Even correct source code can become vulnerable:
- Compiler optimizations might reintroduce early exits
- Branch prediction might leak timing information
- Memory access patterns might vary

**Formal verification proves the SOURCE LOGIC is correct.** Combined with careful compilation (e.g., `volatile` hints, assembly verification), this provides defense in depth.

## Goals

### V1: Plaintext Password (MVP)

1. **Implement** constant-time byte comparison in Rust
2. **Prove** the function examines all bytes (no early exit in logic)
3. **Prove** the result depends only on byte equality
4. **Demonstrate** with a simple CLI that accepts password and returns secret

### V2: Hashed Password (Future)

1. Add bcrypt/argon2 hashing
2. Prove hash comparison is constant-time
3. Explore proving uniqueness of preimage (likely infeasible for crypto hashes)

## Functional Requirements

### FR1: Constant-Time Comparison Function

```rust
/// Compare two byte slices in constant time.
///
/// PROPERTIES TO PROVE:
/// 1. Loop executes exactly min(a.len(), b.len()) iterations
/// 2. No early exit based on byte values
/// 3. Result is true iff all corresponding bytes are equal AND lengths match
pub fn constant_time_eq(a: &[u8], b: &[u8]) -> bool
```

### FR2: Authentication Function

```rust
/// Authenticate a password against stored credential.
/// Returns Some(secret) if correct, None otherwise.
///
/// PROPERTIES TO PROVE:
/// 1. Uses constant_time_eq for comparison
/// 2. Exactly one password value returns Some(_)
pub fn authenticate(input: &[u8], stored: &[u8], secret: &str) -> Option<&str>
```

### FR3: CLI Interface

```
$ echo "hunter2" | cargo run
Access granted: The secret is 42
$ echo "wrong" | cargo run
Unauthorized
```

## Non-Functional Requirements

### NFR1: Aeneas Compatibility

Code must be extractable to Lean:
- No iterator chains (`.map()`, `.filter()`, `.collect()`)
- Explicit `while` loops with index variables
- No complex trait bounds
- No `unsafe` blocks
- No async/await

### NFR2: Proof Coverage

Minimum proofs required:
1. `constant_time_eq` loop bound (executes exactly N times)
2. `constant_time_eq` correctness (returns true iff equal)
3. No early exit property (loop body always executes)

## Technical Design

### Data Flow

```
┌─────────┐     ┌──────────────────┐     ┌─────────────┐
│  stdin  │────▶│  authenticate()  │────▶│   stdout    │
│password │     │                  │     │secret/error │
└─────────┘     └────────┬─────────┘     └─────────────┘
                         │
                         ▼
                ┌──────────────────┐
                │constant_time_eq()│
                │  (VERIFIED)      │
                └──────────────────┘
```

### File Structure

```
rust/src/
├── auth.rs           # Constant-time comparison + authentication
├── lib.rs            # Module exports
└── bin/
    └── auth_demo.rs  # CLI that reads password from stdin
```

### Proof Strategy

#### Property 1: Loop Bound

```lean
theorem loop_bound (a b : List U8) :
  loop_iterations (constant_time_eq a b) = min a.length b.length
```

#### Property 2: Correctness

```lean
theorem eq_correct (a b : List U8) :
  constant_time_eq a b = true ↔ a = b
```

#### Property 3: No Early Exit (Semantic)

We prove that the accumulated `result` variable is computed from ALL byte pairs:

```lean
theorem examines_all_bytes (a b : List U8) (h : a.length = b.length) :
  ∀ i < a.length, (a[i] ⊕ b[i]) contributes to final result
```

This is captured by showing the result equals the OR of all XOR values:

```lean
theorem result_is_full_xor (a b : List U8) (h : a.length = b.length) :
  constant_time_eq_result a b = List.foldl (· ||| ·) 0 (List.zipWith (· ⊕ ·) a b)
```

## Security Considerations

### What We CAN Prove

1. **Logical constant-time**: The source code examines all bytes
2. **Correctness**: Function returns true iff inputs match
3. **Determinism**: Same inputs always produce same outputs

### What We CANNOT Prove (in Lean)

1. **Physical constant-time**: Actual CPU cycles are equal
2. **Compiler preservation**: Optimizer doesn't add branches
3. **Cache timing**: Memory access patterns are uniform
4. **Branch prediction**: CPU speculation doesn't leak

### Mitigation

For production use, combine formal verification with:
- Assembly inspection of compiled output
- Timing measurements in CI
- Use of `subtle` crate (designed for constant-time ops)
- Compilation with `-C opt-level=0` for critical sections

## Success Criteria

### MVP (V1) Complete When:

- [ ] `constant_time_eq` implemented in Aeneas-compatible Rust
- [ ] Charon successfully extracts to LLBC
- [ ] Aeneas generates Lean code
- [ ] At least one non-trivial proof completed (loop bound OR correctness)
- [ ] CLI demo works

### Stretch Goals:

- [ ] Prove all three properties
- [ ] Add timing measurement tests
- [ ] V2: bcrypt integration exploration

## Open Questions

1. **Length comparison**: Should length comparison also be constant-time?
   - Current: Early exit if lengths differ (reveals length info)
   - Alternative: Pad shorter input (hides length but adds complexity)

2. **Empty inputs**: What should `constant_time_eq([], [])` return?
   - Proposed: `true` (vacuously equal)

3. **Overflow handling**: What if inputs are extremely long?
   - Proposed: Accept any length, rely on Rust's bounds checking

## References

- [Timing Attacks on Implementations of Diffie-Hellman, RSA, DSS, and Other Systems](https://www.paulkocher.com/doc/TimingAttacks.pdf) - Kocher, 1996
- [subtle crate](https://docs.rs/subtle/latest/subtle/) - Rust constant-time primitives
- [BearSSL Constant-Time Code](https://bearssl.org/constanttime.html) - Excellent explanation
- [Aeneas Paper](https://dl.acm.org/doi/10.1145/3547647) - Verification methodology
