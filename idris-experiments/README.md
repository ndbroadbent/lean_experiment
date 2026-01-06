# Idris 2 Dependent Types Experiments

Demonstrating how dependent types encode algebraic properties at compile time AND runtime.

## Quick Start

```bash
# Install Idris 2
nix profile add nixpkgs#idris2

# Run the examples
idris2 -o demo PositiveMultiples.idr && ./build/exec/demo
idris2 -o dynproof DynamicProofs.idr && ./build/exec/dynproof
```

## File Overview

| File | Description |
|------|-------------|
| `PositiveMultiples.idr` | Compile-time proofs with static values |
| `DynamicProofs.idr` | Runtime proof construction with dynamic values |
| `ProofDemo.idr` | Explains how proofs work internally |

---

## PositiveMultiples.idr - Compile-Time Proofs

The `PositiveMultiple` type bundles a value with **proofs** of its properties:

```idris
record PositiveMultiple (factor : Nat) where
  constructor MkPosMultiple
  value : Nat
  gtOne : LTE 2 value                        -- Proof: value >= 2
  isMultiple : (k : Nat ** value = k * factor)  -- Proof: value = k * factor
```

### Type-Safe Function Constraints

```idris
-- This function ONLY accepts multiples of 7
processMultipleOf7 : PositiveMultiple 7 -> Nat

example1 : PositiveMultiple 3   -- (5 * 3 = 15)
example2 : PositiveMultiple 7   -- (4 * 7 = 28)

processMultipleOf7 example2  -- ✓ Compiles
processMultipleOf7 example1  -- ✗ TYPE ERROR: can't unify 3 with 7
```

---

## DynamicProofs.idr - Runtime Proof Construction

**Q: Can you prove properties about values from stdin?**

**A: Yes!** Proofs are constructed at runtime. If construction fails, the code path requiring proofs is unreachable.

```
$ ./build/exec/dynproof
=== Dynamic Proof Construction ===

Test 1: n=15, factor=5
  SUCCESS: 15 is >= 2 AND is 3 x 5    ← proof constructed

Test 2: n=15, factor=7
  REJECTED: 15 is not a multiple of 7 ← no valid proof exists

Test 3: n=1, factor=3
  REJECTED: 1 is not >= 2             ← no valid proof exists
```

### How Runtime Proofs Work

```idris
checkMultipleOf n factor =
  case decEq n (q * factor) of      -- Attempt to construct proof
    Yes prf => Right (MkMultipleOf n q prf)  -- Success: real proof
    No _    => Left "not a multiple"          -- Failure: no proof possible
```

---

## Are These "Real" Proofs?

**Yes.** This is NOT "trust me" typing. The proofs are values that must be constructed.

### The LTE (Less Than or Equal) Proof Type

```idris
data LTE : Nat -> Nat -> Type where
  LTEZero : LTE 0 n                     -- Base: 0 <= anything
  LTESucc : LTE m n -> LTE (S m) (S n)  -- Step: m<=n implies m+1<=n+1
```

To prove `LTE 2 5`, you must build it with constructors:

```idris
proof_2_lte_5 : LTE 2 5
proof_2_lte_5 = LTESucc (LTESucc LTEZero)
--              ^^^^^^^ ^^^^^^^ ^^^^^^^
--              1<=4    0<=3    0<=3 (base)
```

You **cannot** construct `LTE 5 2` - no valid sequence of constructors exists!

### The Equality Proof Type

`Refl` has type `x = x`. It only typechecks when both sides are **definitionally equal**:

```idris
good : 15 = 5 * 3
good = Refl   -- ✓ Compiler computes 5*3=15, so "15=15" checks

bad : 15 = 4 * 3
bad = Refl    -- ✗ Compiler computes 4*3=12, "15=12" REJECTED
```

### The Trust Chain for Dynamic Proofs

```
decEq n (q * factor)          -- stdlib function, computes equality
         ↓
   [runtime computation]
         ↓
Yes prf : n = q * factor      -- Only returned if actually equal
         ↓
MkMultipleOf n q prf          -- We forward the proof, don't create it
         ↓
Type checker verifies prf has correct type
```

We don't "say" what the proof means - we **forward** a proof that `decEq` constructed. If `decEq` returns `No`, we have no proof to forward.

---

## Why Not Just Use Runtime Checks?

Traditional approach:
```python
def process(n, factor):
    if n >= 2 and n % factor == 0:
        do_stuff(n)  # Hope n still has those properties...
```

Problem: Nothing stops you from calling `do_stuff(1)` elsewhere.

Dependent types approach:
```idris
processVerified : AtLeast2 -> MultipleOf factor -> String
-- IMPOSSIBLE to call without proofs. The type system enforces it.
```

---

## Compile vs Runtime Execution

```
Source Code
     ↓
[Type Checker]  ← Proofs verified here (computations happen)
     ↓
[Compiler]      ← Proofs ERASED (zero runtime overhead)
     ↓
Native Binary   ← Fast, no proof data at runtime
```

At runtime, `AtLeast2` is just a `Nat` - the `LTE 2 value` proof is erased. It served its purpose (convincing the compiler) and adds zero overhead.

---

## Limitations

- `Nat` is unary (like tally marks) - very slow for large numbers
- For production, use `Integer` with separate proof-carrying types
- Some proofs require manual construction or tactics

---

## Key Takeaways

1. **Types can depend on values** - `PositiveMultiple 7` is different from `PositiveMultiple 3`
2. **Proofs are values** - must be constructed, can't be faked
3. **Runtime proof construction** - `decEq` computes and returns evidence
4. **Proof erasure** - proofs exist at compile time, gone at runtime
5. **Type-safe APIs** - impossible to call functions without required proofs
