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

### CRITICAL: Aeneas/Charon Installation

**NEVER use `nix run github:...` - this downloads and recompiles from scratch every time!**

Aeneas does NOT have a binary cache (no cachix). The first install compiles ~308 derivations including OCaml, Rust nightly, and the entire toolchain. This takes 10-20+ minutes but only needs to happen ONCE.

**Install aeneas globally with `nix profile add`:**
```bash
# Install aeneas (includes charon as a symlink)
# First run takes a long time (~10-20 min) - this is normal
nix profile add github:aeneasverif/aeneas#aeneas

# Verify installation
nix profile list
ls ~/.nix-profile/bin/  # Should show aeneas and charon
```

**IMPORTANT:** Only install `#aeneas` - do NOT install both `#charon` and `#aeneas` together, as this causes a conflict (both provide the `charon` binary).

**If installation fails:**
1. Check `nix profile list` to see current state
2. Remove failed entries: `nix profile remove <name>` (e.g., `nix profile remove aeneas`)
3. Retry the install command
4. On macOS, ensure Xcode command line tools are installed

**After installation**, `charon` and `aeneas` are available in `~/.nix-profile/bin/`. Ensure this is in your PATH:
```bash
# Add to your shell profile if not already present:
export PATH="$HOME/.nix-profile/bin:$PATH"
```

**Verify tools work:**
```bash
charon --help
aeneas -help
```
(Note: These tools use `-help` not `--version`)

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
