# Formally Verified String Library

## Vision

Build a formally verified string library from first principles, proving security properties about password handling with mathematical certainty.

## Core Insight

Strings are vectors of integers. UTF-8 is a vector of vectors.

```
ASCII string:  [u8; n]           → Vector in ℤ₂₅₆ⁿ
UTF-8 string:  [[u8; 1-4]; m]    → Vector of vectors (variable inner length)
```

The flat byte stream `[104, 195, 169, 108, 108, 111]` is serialization.
The true structure is `[[104], [195, 169], [108], [108], [111]]` ("héllo").

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                         UNTRUSTED ZONE                          │
│  stdin/stdout, network, filesystem, user input                  │
│  Type: String (Rust std library)                                │
└─────────────────────────────────────────────────────────────────┘
                               │
                               ▼
┌─────────────────────────────────────────────────────────────────┐
│                      BOUNDARY (unsafe/sorry)                    │
│  • string.as_bytes() → Vec<u8>                                  │
│  • UNVERIFIED but trivial: identity at byte level               │
│  • This is the "shoehorn" that lets us use strings              │
└─────────────────────────────────────────────────────────────────┘
                               │
                               ▼
┌─────────────────────────────────────────────────────────────────┐
│                        VERIFIED CORE                            │
│  Type: Vec<u8>, [[u8; 1-4]], pure numbers                       │
│  • UTF-8 parsing (bytes → vector of vectors)                    │
│  • Constant-time comparison                                     │
│  • Password checking                                            │
│  • Secret revelation                                            │
│  • ALL PROVEN via Aeneas: correctness, constant-time, etc.      │
└─────────────────────────────────────────────────────────────────┘
                               │
                               ▼
┌─────────────────────────────────────────────────────────────────┐
│                      BOUNDARY (unsafe/sorry)                    │
│  • String::from_utf8(bytes) → String                            │
│  • UNVERIFIED but trivial: identity at byte level               │
└─────────────────────────────────────────────────────────────────┘
                               │
                               ▼
┌─────────────────────────────────────────────────────────────────┐
│                         UNTRUSTED ZONE                          │
│  Type: String (back to Rust std library)                        │
└─────────────────────────────────────────────────────────────────┘
```

## The Boundary Layer Strategy

### The Problem

Aeneas/Charon don't support Rust's `String` type — it relies on heap allocation,
complex std library internals, and string literals which Aeneas can't translate.

### The Solution

We prove everything on **pure numbers** (vectors of u8), then wrap in a thin
boundary layer that converts between `String` and `Vec<u8>`.

```rust
// BOUNDARY: Unverified, but trivially correct
mod boundary {
    /// Convert String to bytes - this is literally just exposing the internal buffer
    pub fn string_to_bytes(s: &str) -> &[u8] {
        s.as_bytes()  // Zero-cost, same memory
    }

    /// Convert bytes to String - validates UTF-8
    pub fn bytes_to_string(bytes: Vec<u8>) -> Result<String, FromUtf8Error> {
        String::from_utf8(bytes)  // Just a type wrapper
    }
}

// VERIFIED CORE: All proofs happen here on pure numbers
mod verified {
    pub fn constant_time_eq(a: &[u8], b: &[u8]) -> bool { ... }
    pub fn check_password(input: &[u8], stored: &[u8]) -> bool { ... }
    // ... all proven via Aeneas
}

// PUBLIC API: Combines boundary + verified core
pub fn check_password_string(input: &str, stored: &str) -> bool {
    let input_bytes = boundary::string_to_bytes(input);
    let stored_bytes = boundary::string_to_bytes(stored);
    verified::check_password(input_bytes, stored_bytes)
}
```

### Why This Works

1. **`String` IS `Vec<u8>` internally** — Rust guarantees this
2. **`as_bytes()` is zero-cost** — no conversion, just type change
3. **The mapping is 1:1** — every string operation maps to a byte operation
4. **Proofs transfer** — if we prove `f(bytes) = result`, then `f(string.as_bytes()) = result`

### The "sorry" in Lean

In the Lean proofs, we'd mark the boundary layer with `sorry` (unproven axiom):

```lean
-- BOUNDARY: We axiomatically accept that String ↔ Vec<u8> is identity
axiom string_to_bytes_identity : ∀ s : String, (string_to_bytes s) = s.toUTF8
axiom bytes_to_string_identity : ∀ b : Vec U8, valid_utf8 b → (bytes_to_string b).toUTF8 = b

-- VERIFIED: Everything else is proven
theorem password_correct : ∀ input stored,
  check_password input stored = (input = stored) := by
  -- ... actual proof
```

### Trust Model

```
┌────────────────────────────────────────────────────────────────┐
│                    WHAT WE PROVE (Verified)                    │
│  • Algorithm correctness on byte vectors                       │
│  • Constant-time property                                      │
│  • UTF-8 parsing correctness                                   │
│  • Secret revelation logic                                     │
└────────────────────────────────────────────────────────────────┘

┌────────────────────────────────────────────────────────────────┐
│                    WHAT WE ASSUME (Axioms)                     │
│  • Rust's String is a valid UTF-8 Vec<u8>                      │
│  • as_bytes() returns the actual internal bytes                │
│  • from_utf8() correctly validates and wraps bytes             │
│  These are guaranteed by Rust's std library specification.     │
└────────────────────────────────────────────────────────────────┘

┌────────────────────────────────────────────────────────────────┐
│                    WHAT WE DON'T VERIFY                        │
│  • Rust compiler correctness                                   │
│  • Standard library implementation                             │
│  • OS/hardware behavior                                        │
│  • Cryptographic primitive security (SHA-256 etc)              │
└────────────────────────────────────────────────────────────────┘
```

### Performance Note

The boundary layer has **zero runtime overhead**:
- `as_bytes()` is a pointer cast, not a copy
- `from_utf8()` validates but doesn't copy (or use `from_utf8_unchecked` if pre-validated)

So we get formal verification of the algorithm with production-grade performance.

## The UTF-8 Parser

### Mathematical Model

UTF-8 encoding uses leading bits to define groupings:

```
0xxxxxxx              → 1-byte sequence (ASCII)
110xxxxx 10xxxxxx     → 2-byte sequence
1110xxxx 10xxxxxx × 2 → 3-byte sequence
11110xxx 10xxxxxx × 3 → 4-byte sequence
```

### Type Definition

```rust
/// A parsed UTF-8 code point (1-4 bytes)
pub struct CodePoint {
    bytes: [u8; 4],  // The raw bytes
    len: u8,         // How many bytes are valid (1-4)
}

/// A parsed UTF-8 string = vector of code points
pub struct Utf8String {
    code_points: Vec<CodePoint>,  // Vector of vectors (conceptually)
}
```

### Properties to Prove

1. **Parsing is total**: Every byte sequence produces a result (valid or error)
2. **Valid UTF-8 roundtrips**: `serialize(parse(bytes)) = bytes` for valid UTF-8
3. **Length preservation**: `sum(code_point.len for cp in parsed) = bytes.len`
4. **No panics**: Parser handles all inputs without panic

## Constant-Time Password Comparison

### The Problem

Naive comparison leaks timing information:

```rust
// VULNERABLE: early exit reveals password length and prefix
fn check_password(input: &[u8], secret: &[u8]) -> bool {
    if input.len() != secret.len() { return false; }  // Leaks length!
    for i in 0..input.len() {
        if input[i] != secret[i] { return false; }    // Leaks prefix!
    }
    true
}
```

### The Solution

```rust
/// Constant-time comparison: always examines all bytes
pub fn constant_time_eq(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;  // Length check is unavoidable, but use fixed-length passwords
    }

    let mut result: u8 = 0;
    for i in 0..a.len() {
        result |= a[i] ^ b[i];  // Accumulate differences, no early exit
    }
    result == 0
}
```

### Properties to Prove

1. **Correctness**: `constant_time_eq(a, b) = true ↔ a = b`
2. **No early exit**: Loop always runs `n` iterations regardless of input
3. **Constant operations**: Each iteration performs the same operations

## Secret Revelation

### The Model

```rust
const SECRET: &str = "The answer is 42";
const PASSWORD_HASH: [u8; 32] = [...];  // SHA-256 of correct password

pub fn get_secret(password: &[u8]) -> Option<&'static str> {
    let hash = sha256(password);
    if constant_time_eq(&hash, &PASSWORD_HASH) {
        Some(SECRET)
    } else {
        None
    }
}
```

### Properties to Prove

1. **Correct password succeeds**: `∀ correct_pwd. hash(correct_pwd) = PASSWORD_HASH → get_secret(correct_pwd) = Some(SECRET)`
2. **Wrong password fails**: `∀ wrong_pwd. hash(wrong_pwd) ≠ PASSWORD_HASH → get_secret(wrong_pwd) = None`
3. **No other path to secret**: The only way to obtain `SECRET` is through this function with correct password

## Implementation Roadmap

### Phase 1: UTF-8 Parser (Foundation)

```rust
// rust/src/utf8.rs

/// Determine the length of a UTF-8 sequence from its first byte
pub fn sequence_length(first_byte: u8) -> u8 {
    if first_byte & 0x80 == 0 { 1 }        // 0xxxxxxx
    else if first_byte & 0xE0 == 0xC0 { 2 } // 110xxxxx
    else if first_byte & 0xF0 == 0xE0 { 3 } // 1110xxxx
    else if first_byte & 0xF8 == 0xF0 { 4 } // 11110xxx
    else { 0 }  // Invalid
}

/// Check if a byte is a valid continuation byte
pub fn is_continuation(byte: u8) -> bool {
    byte & 0xC0 == 0x80  // 10xxxxxx
}

/// Parse a single code point from bytes, return (code_point_bytes, length)
pub fn parse_code_point(bytes: &[u8]) -> Option<(u32, u8)> {
    // ... implementation
}

/// Parse entire byte slice into vector of code points
pub fn parse_utf8(bytes: &[u8]) -> Result<Vec<[u8; 4]>, usize> {
    // Returns Ok(code_points) or Err(byte_index_of_error)
}
```

### Phase 2: Constant-Time Comparison

```rust
// rust/src/constant_time.rs

/// XOR all bytes, accumulate result
pub fn constant_time_eq(a: &[u8], b: &[u8]) -> bool {
    // Must be same length for constant-time property
    assert_eq!(a.len(), b.len());

    let mut acc: u8 = 0;
    for i in 0..a.len() {
        acc |= a[i] ^ b[i];
    }
    acc == 0
}
```

### Phase 3: Password Checker POC

```rust
// rust/src/password.rs

const SECRET: &[u8] = b"The treasure is buried under the old oak tree";
const PASSWORD: &[u8] = b"hunter42";  // In real app, store hash

pub fn check_and_reveal(input: &[u8]) -> Option<&'static [u8]> {
    if constant_time_eq(input, PASSWORD) {
        Some(SECRET)
    } else {
        None
    }
}
```

## Proofs Structure

```
CharsProofs.lean          # Character/byte operations (DONE)
Utf8Proofs.lean           # UTF-8 parsing proofs
  ├── sequence_length_valid
  ├── parse_roundtrip
  └── parse_total
ConstantTimeProofs.lean   # Constant-time comparison proofs
  ├── constant_time_eq_correct
  ├── no_early_exit
  └── operations_uniform
PasswordProofs.lean       # Password checker proofs
  ├── correct_password_reveals_secret
  ├── wrong_password_reveals_nothing
  └── secret_only_via_correct_password
```

## Security Model

### What We Prove

1. **Functional correctness**: The code does what it's supposed to do
2. **No timing side-channels**: Comparison takes same time for all inputs (of same length)
3. **Information flow**: Secret only flows to output on correct password

### What We Don't Prove (Out of Scope)

1. **Cryptographic hash security**: We assume SHA-256 is secure
2. **Hardware side-channels**: CPU cache timing, power analysis, etc.
3. **Memory safety**: Handled by Rust's type system
4. **Compiler correctness**: Assumed

### Trust Boundaries

```
UNTRUSTED          DMZ              VERIFIED           DMZ           UNTRUSTED
   │                │                  │                │                │
   │   raw bytes    │  parsed UTF-8    │   comparison   │  serialized    │
   ├───────────────►├─────────────────►├───────────────►├───────────────►│
   │                │                  │                │                │
   │                │◄─── PROVEN ─────►│◄─── PROVEN ───►│                │
```

## Connection to Existing Work

- `chars.rs` / `CharsProofs.lean`: MVP of bytes ↔ integers (COMPLETE)
- `CHARACTER_CONCATENATION.md`: Mathematical foundation for string ops
- `SecurityDuality.lean`: Framework for thinking about proofs as security
- `LIST_OF_IDEAS.md`: Overview of all ideas

## Next Steps

1. Implement `utf8.rs` with `sequence_length`, `is_continuation`, `parse_code_point`
2. Run through Aeneas pipeline
3. Write `Utf8Proofs.lean` proving parsing properties
4. Implement `constant_time.rs`
5. Prove constant-time property in Lean
6. Build the password checker POC
7. Prove secret revelation properties
