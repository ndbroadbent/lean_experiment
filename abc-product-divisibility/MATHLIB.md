# Mathlib Reference for ABC Product Divisibility

## Key Imports

```lean
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Defs
import Mathlib.Data.Nat.Prime.Basic
```

## p-adic Valuation (`padicValNat`)

The p-adic valuation `padicValNat p n` gives the largest k such that p^k divides n.

### Core Lemmas

```lean
-- Valuation of a product is sum of valuations
padicValNat.mul : a ≠ 0 → b ≠ 0 → padicValNat p (a * b) = padicValNat p a + padicValNat p b

-- Divisibility iff valuation inequality (KEY for our proof!)
padicValNat_dvd_iff_le [Fact p.Prime] {a n : ℕ} (ha : a ≠ 0) :
    p ^ n ∣ a ↔ n ≤ padicValNat p a

-- Valuation of prime power
padicValNat.prime_pow (n : ℕ) : padicValNat p (p ^ n) = n

-- Valuation of different prime is 0
padicValNat_primes [Fact p.Prime] [Fact q.Prime] (neq : p ≠ q) : padicValNat p q = 0

-- Valuation of prime power of different prime
padicValNat_prime_prime_pow [Fact p.Prime] [Fact q.Prime] (n : ℕ) (neq : p ≠ q) :
    padicValNat p (q ^ n) = 0

-- Combined: valuation of p^n * q^m
padicValNat_mul_pow_left [Fact p.Prime] [Fact q.Prime] (n m : ℕ) (neq : p ≠ q) :
    padicValNat p (p^n * q^m) = n
```

### Location
- `Mathlib/NumberTheory/Padics/PadicVal/Basic.lean`
- `Mathlib/NumberTheory/Padics/PadicVal/Defs.lean`

## Prime Divisibility

```lean
-- Prime divides product iff divides one factor
Nat.Prime.dvd_mul {p m n : ℕ} (hp : p.Prime) : p ∣ m * n ↔ p ∣ m ∨ p ∣ n

-- From Mathlib.Data.Nat.Prime.Basic
```

## Strategy for ABC Proof

The key insight: if `p² ∣ xyz` then `padicValNat p (xyz) ≥ 2`.

By `padicValNat.mul`:
```
padicValNat p (xyz) = padicValNat p x + padicValNat p y + padicValNat p z
```

So we need:
```
padicValNat p x + padicValNat p y + padicValNat p z ≥ 2
```

For our specific case with p=7, q=11, r=13:
- `abc = p²q²r²`
- Need `padicValNat p (xyz) ≥ 2` for each of p, q, r
- Total: sum of all 9 valuations ≥ 6

The pigeonhole: with 3 numbers and needing 6 total, if at most one number contributes to multiple primes, we can't reach 6.

## Key Iff Lemmas

```lean
-- Valuation = 0 characterization
padicValNat.eq_zero_iff {n : ℕ} : padicValNat p n = 0 ↔ p = 1 ∨ n = 0 ∨ ¬p ∣ n

-- Divisibility iff valuation ≥ 1
dvd_iff_padicValNat_ne_zero [Fact p.Prime] (hn0 : n ≠ 0) :
    p ∣ n ↔ padicValNat p n ≠ 0

-- p^(v+1) does NOT divide n
pow_succ_padicValNat_not_dvd [Fact p.Prime] (hn : n ≠ 0) :
    ¬p ^ (padicValNat p n + 1) ∣ n
```

## Useful Tactics

- `decide` / `native_decide` for concrete computations
- `omega` for linear arithmetic
- `interval_cases x` when x is bounded
- `simp [padicValNat.mul, ...]` to unfold valuations

## Decidability

`padicValNat` is computable! Can use `native_decide` for concrete values:
```lean
example : padicValNat 7 6006 = 1 := by native_decide
example : padicValNat 11 6006 = 1 := by native_decide
example : padicValNat 13 6006 = 1 := by native_decide
```
