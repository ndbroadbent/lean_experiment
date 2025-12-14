# Password Verifier - Formally Verified Constant-Time Password Checking

Self-contained project for verifying a password-protected secret using constant-time comparison.

## What This Proves

1. **Correctness**: `ct_eq_bytes(a, b) = true ↔ a = b`
2. **Constant-time structure**: No early-exit branches in comparison
3. **Security**: Only correct password reveals the secret

## Build Commands

```bash
# Rust
cd rust && cargo test

# Generate Lean from Rust
cd rust && charon && aeneas -backend lean password_verifier.llbc

# Build Lean proofs
lake build
```

## Files

```
rust/src/
├── constant_time.rs   # ct_eq_bytes - constant-time byte comparison
└── password.rs        # check_password, reveal_secret

PasswordVerifier.lean  # Aeneas-generated (DO NOT EDIT)
PasswordProofs.lean    # Formal proofs
```

## Proof Layers

```
Layer 0: Bit-level
├── U8.xor_self, U8.or_eq_zero_iff, U8.xor_eq_zero_iff

Layer 1: Primitive
├── ct_eq_bytes_refl, ct_eq_bytes_correct

Layer 2: Construction
├── check_password_correct, reveal_secret_security
```
