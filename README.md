# Lean Experiment: Verified Rust

A project exploring formal verification of Rust programs using Lean 4 via the Aeneas toolchain.

## Project Structure

```
.
├── rust/                    # Rust code to verify
│   └── src/
│       ├── lib.rs          # Module root
│       ├── math.rs         # Arithmetic operations
│       ├── strings.rs      # String operations
│       └── fibonacci.rs    # Fibonacci implementations
├── LeanExperiment/         # Lean 4 proofs and examples
│   ├── Basic.lean
│   ├── Example1_Arithmetic.lean
│   ├── Example2_Strings.lean
│   ├── Example3_Monads.lean
│   ├── Example4_IO.lean
│   └── Example5_Validation.lean
├── lakefile.toml           # Lean build config
└── lean-toolchain          # Lean version
```

## Prerequisites

- **Rust**: Install via [rustup](https://rustup.rs)
- **Lean 4**: Install via elan: `curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh`
- **Nix**: Install via [Determinate Systems](https://install.determinate.systems): `curl --proto '=https' --tlsv1.2 -sSf -L https://install.determinate.systems/nix | sh -s -- install`

## Running the Code

### Rust

```bash
cd rust
cargo test    # Run tests
cargo run     # Run demo
```

### Lean

```bash
source ~/.elan/env
lake build    # Build all Lean code
```

## Verification Workflow (Aeneas)

[Aeneas](https://github.com/AeneasVerif/aeneas) translates Rust to pure Lean code for verification.

### Step 1: Extract Rust MIR with Charon

```bash
cd rust
nix run github:aeneasverif/aeneas#charon
# Creates: verified_rust.llbc
```

### Step 2: Translate to Lean with Aeneas

```bash
nix run github:aeneasverif/aeneas -- -backend lean verified_rust.llbc
# Creates: Lean files in output directory
```

### Step 3: Write Proofs

The generated Lean code represents your Rust functions as pure functions.
You can then write theorems about them:

```lean
-- Example: Prove that our GCD is commutative
theorem gcd_comm (a b : U32) : gcd a b = gcd b a := by
  -- proof here
```

## What Can Be Verified?

Aeneas works best with:
- Pure functions (no global state)
- Safe Rust (no `unsafe` blocks)
- Bounded loops / recursion
- Simple data structures (no complex trait objects)

Limitations:
- No async/await
- Limited standard library support
- No FFI

## Example Properties to Verify

### Math (`rust/src/math.rs`)
- `add(a, b) = add(b, a)` (commutativity)
- `gcd(a, b) = gcd(b, a)` (commutativity)
- `factorial(0) = 1`
- `is_prime(2) = true`

### Fibonacci (`rust/src/fibonacci.rs`)
- `fib(0) = 0`
- `fib(1) = 1`
- `fib(n) = fib(n-1) + fib(n-2)` for n ≥ 2
- `fib_iter(n) = fib_matrix(n)` (implementation equivalence)

### Strings (`rust/src/strings.rs`)
- `validate_and_process(s).is_none()` when `s.len() > 10`
- `validate_and_process("hello") = Some("hello world")`

## Resources

- [Aeneas GitHub](https://github.com/AeneasVerif/aeneas)
- [Charon GitHub](https://github.com/AeneasVerif/charon)
- [Lean 4 Documentation](https://lean-lang.org/lean4/doc/)
- [Aeneas Paper](https://dl.acm.org/doi/10.1145/3547647)
