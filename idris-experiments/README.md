# Idris 2 Dependent Types Experiments

Demonstrating how dependent types encode algebraic properties at compile time.

## PositiveMultiples.idr

This module showcases dependent types for proving properties about positive number multiplication.

### Key Concept

The `PositiveMultiple` type bundles a value with **proofs** of its properties:

```idris
record PositiveMultiple (factor : Nat) where
  constructor MkPosMultiple
  value : Nat
  gtOne : LTE 2 value           -- Proof: value >= 2
  isMultiple : (k : Nat ** value = k * factor)  -- Proof: value = k * factor
```

### What We Prove

1. **Multiplying two numbers >= 2 always produces a result >= 2**
2. **The result is always a multiple of the second factor**
3. **These properties are encoded in the type itself**

### The Power of Dependent Types

```idris
-- This function ONLY accepts multiples of 7
processMultipleOf7 : PositiveMultiple 7 -> Nat

-- example1 is a PositiveMultiple 3 (from 5 * 3 = 15)
-- example2 is a PositiveMultiple 7 (from 4 * 7 = 28)

exampleUsage7 = processMultipleOf7 example2  -- Compiles!
badExample    = processMultipleOf7 example1  -- TYPE ERROR!
```

The compiler **rejects** passing a `PositiveMultiple 3` to a function expecting `PositiveMultiple 7`:

```
Error: When unifying:
    PositiveMultiple 3
and:
    PositiveMultiple 7
Mismatch between: 0 and 4.
```

### Running

```bash
# Install Idris 2
nix profile add nixpkgs#idris2

# Typecheck
idris2 --check PositiveMultiples.idr

# Run example
idris2 PositiveMultiples.idr -x 'printLn exampleUsage'
# Output: "Value: 15 is a multiple of the factor and is >= 2"
```

### Why This Matters

- **Compile-time guarantees**: Invalid states are unrepresentable
- **Self-documenting**: The type signature tells you exactly what properties are required
- **No runtime checks needed**: The proof is verified at compile time and erased at runtime
- **Composable**: Functions can require and produce refined types, chaining guarantees

### Functions That Require Proofs

```idris
-- Only accepts numbers that are:
-- 1. >= 2
-- 2. A multiple of the specified factor
onlyAcceptsRefinedType : {factor : Nat} -> PositiveMultiple factor -> String

-- Even more specific: must be a multiple of 5 AND >= 10
requiresMultOf5 : (pm : PositiveMultiple 5) -> (p : LTE 10 (getValue pm)) -> String
```
