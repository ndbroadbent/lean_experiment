# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a Lean 4 project for formal verification of Rust programs using the Aeneas toolchain. Rust code is translated to pure Lean functions, and proofs are written to verify properties about the Rust code.

## Project Structure

```
lean_experiment/
├── password-verifier/     # Self-contained password verification project
│   ├── rust/src/          # constant_time.rs, password.rs
│   ├── PasswordVerifier.lean  # Aeneas-generated
│   └── PasswordProofs.lean    # Proofs
│
├── utf8-parser/           # Self-contained UTF-8 parser project
│   ├── rust/src/          # utf8.rs
│   ├── Utf8Parser.lean    # Aeneas-generated
│   └── Utf8Proofs.lean    # Proofs
│
└── experiments/           # Unverified experiments (fibonacci, math, etc.)
    └── rust/src/
```

## Tool Installation

**IMPORTANT: NEVER use `nix run github:...` - this recompiles from scratch every time!**

Install tools once with `nix profile add`:
```bash
nix profile add github:aeneasverif/aeneas#charon
nix profile add github:aeneasverif/aeneas#aeneas
```

After installation, `charon` and `aeneas` are available directly in your PATH.

## Build Commands

### Lean
```bash
lake build           # Build all Lean code
```

### Rust
```bash
cd rust
cargo test           # Run Rust tests
cargo build          # Build Rust code
```

### Aeneas Verification Workflow
```bash
cd rust

# Step 1: Extract Rust MIR with Charon (uses installed binary)
charon cargo --preset=aeneas
# Creates: <crate_name>.llbc

# Step 2: Translate to Lean with Aeneas (uses installed binary)
aeneas -backend lean -dest .. <crate_name>.llbc
# Creates: Lean files in parent directory
```

## Key Libraries

- **Aeneas**: Provides `Aeneas.Std`, `Result`, `U32`, and related types for representing Rust semantics in Lean
- **Mathlib**: Available via Aeneas dependencies for mathematical proofs

## Aeneas-Specific Patterns

### Result Type
Rust functions become Lean functions returning `Result T` to handle potential panics/overflows:
```lean
def simple.add (a : U32) (b : U32) : Result U32 := do
  a + b
```

### Proving Properties
Use `simp`, `omega`, and Aeneas lemmas (e.g., `U32.add_comm`, `U32.mul_one`):
```lean
theorem add_comm (a b : U32) (h : (a + b).isOk) :
    add a b = add b a := by
  simp only [add]
  rw [U32.add_comm]
```

### Partial Fixpoints
Recursive Rust functions use `partial_fixpoint` annotation in the generated Lean code.

## Rust Code Guidelines for Verification

Aeneas works best with:
- Pure functions (no global state)
- Safe Rust (no `unsafe` blocks)
- Bounded loops / recursion
- Simple data structures

Avoid: async/await, complex trait objects, FFI, most of std library, `String`, `Vec` with complex operations.
