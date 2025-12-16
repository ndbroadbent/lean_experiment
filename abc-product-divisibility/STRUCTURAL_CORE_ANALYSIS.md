# Structural Core Analysis: Toward a Pure Symbolic Proof

This document captures the exploration of Mathlib lemmas and strategies for building a purely structural proof of the ABC product divisibility counterexample - one with **no `decide`, no `native_decide`, no `omega` on concrete numbers**.

---

## Goal

Write a proof where:
- The structural argument is entirely symbolic
- Concrete numbers (7, 11, 13, 6006, etc.) appear only as witnesses
- All reasoning chains through abstract lemmas about divisibility, coprimality, and intervals

---

## Part 1: Key Mathlib Lemmas Discovered

### 1.1 p-adic Valuation Core

| Lemma | Location | Signature | Use |
|-------|----------|-----------|-----|
| `padicValNat.mul` | PadicVal/Basic.lean:398 | `padicValNat p (a * b) = padicValNat p a + padicValNat p b` | Additivity for products |
| `padicValNat_dvd_iff_le` | PadicVal/Basic.lean:446 | `p^n ∣ a ↔ n ≤ padicValNat p a` (when a ≠ 0) | Divisibility ↔ valuation |
| `padicValNat_dvd_iff` | PadicVal/Basic.lean:451 | `p^n ∣ a ↔ a = 0 ∨ n ≤ padicValNat p a` | Zero-friendly version |
| `pow_padicValNat_dvd` | PadicVal/Basic.lean:440 | `p ^ padicValNat p n ∣ n` | Exponent bounds divisibility |
| `pow_succ_padicValNat_not_dvd` | PadicVal/Basic.lean:457 | `¬p ^ (padicValNat p n + 1) ∣ n` | Maximality |
| `dvd_of_one_le_padicValNat` | PadicVal/Basic.lean:435 | `1 ≤ padicValNat p n → p ∣ n` | Nonzero valuation → divisibility |
| `one_le_padicValNat_of_dvd` | PadicVal/Basic.lean:211 | `p ∣ n → n ≠ 0 → 1 ≤ padicValNat p n` | Divisibility → nonzero valuation |

### 1.2 Distinct Primes and Coprimality

| Lemma | Location | Signature | Use |
|-------|----------|-----------|-----|
| `coprime_primes` | Prime/Basic.lean:194 | `Coprime p q ↔ p ≠ q` (for primes) | **Key**: distinct primes are coprime |
| `coprime_pow_primes` | Prime/Basic.lean:197 | `Coprime (p^n) (q^m)` (for p ≠ q primes) | Powers of distinct primes |
| `padicValNat_primes` | PadicVal/Basic.lean:462 | `padicValNat p q = 0` (p ≠ q primes) | Different prime has zero valuation |
| `padicValNat_prime_prime_pow` | PadicVal/Basic.lean:467 | `padicValNat p (q^n) = 0` (p ≠ q) | Powers too |
| `Prime.dvd_mul_of_dvd_ne` | Prime/Basic.lean:218 | If p ≠ q primes both divide n, then pq ∣ n | **Critical for pq divisibility** |

### 1.3 Coprime Divisibility

| Lemma | Location | Signature | Use |
|-------|----------|-----------|-----|
| `IsCoprime.mul_dvd` | Coprime/Basic.lean:114 | If x,y coprime and both divide z, then xy ∣ z | Generic coprime product |
| `Nat.Coprime.mul_dvd_of_dvd_of_dvd` | (Nat version) | Same for Nat.Coprime | The one we've been using |
| `Finset.prod_dvd_of_coprime` | Coprime/Lemmas.lean:93 | Pairwise coprime divisors → product divides | Generalizes to n factors |

### 1.4 Interval and Multiple Counting

| Lemma | Location | Signature | Use |
|-------|----------|-----------|-----|
| `padicValNat_eq_zero_of_mem_Ioo` | PadicVal/Basic.lean:547 | `m ∈ Ioo (p*k) (p*(k+1)) → padicValNat p m = 0` | **Structural "at most one multiple"** |
| `Int.Ico_filter_dvd_card` | CardIntervalMod.lean | `#{x ∈ Ico a b \| r ∣ x} = max (⌈b/r⌉ - ⌈a/r⌉) 0` | Exact count of multiples |
| `Nat.card_multiples` | Factorization/Basic.lean | `#{e ∈ range n \| p ∣ e+1} = n / p` | Alternative counting |
| `Nat.mod_injOn_Ico` | Interval/Finset/Nat.lean | Mod is injective on intervals of width a | At most one per residue class |

### 1.5 Modular Arithmetic

| Lemma | Location | Use |
|-------|----------|-----|
| `Nat.ModEq` | Various | Congruence relations |
| `Nat.modEq_iff_dvd` | | Connects congruence to divisibility |
| `Nat.dvd_sub` | | m ∣ a → m ∣ b → m ∣ (a - b) |
| `Nat.eq_zero_of_dvd_of_lt` | | m ∣ t → t < m → t = 0 |

---

## Part 2: The Toolkit Approach

Instead of proving window facts by computation, build **symbolic lemmas** that derive facts from:
- Window is centered at N
- Radius is < m
- m ∣ N
- Primes are coprime
- Congruence conditions

### 2.1 Unique Multiple in Centered Window

**Statement**: If `m ∣ N` and `d < m`, then any `x` with `|x - N| ≤ d` and `m ∣ x` must equal `N`.

**Proof sketch**:
1. From `m ∣ x` and `m ∣ N`, get `m ∣ (x - N)`
2. But `|x - N| ≤ d < m`
3. Only multiple of m with absolute value < m is 0
4. So x = N

**Mathlib building blocks**:
- `Nat.dvd_sub` (with order hypotheses)
- `Nat.eq_zero_of_dvd_of_lt`: if m ∣ t and t < m then t = 0

This replaces `only_6006_div_77` with:
```
m = 77, N = 6006, d = 71
show d < m  -- structural
apply unique_multiple_lemma
```

### 2.2 Avoid Residue Class in Centered Window

**Statement**: If `d < m/2` and `N mod m ∈ (d, m-d)`, then `∀ x, |x - N| ≤ d → ¬(m ∣ x)`.

**Proof sketch**:
1. If m ∣ x, then x ≡ 0 (mod m)
2. But x is within d of N, so x mod m is within d of (N mod m)
3. Since N mod m is far from 0 (distance > d), x mod m ≠ 0
4. Contradiction

This replaces `no_169_in_window`:
```
m = 169, d = 71, N mod 169 = 87 (which is in (71, 98))
```

### 2.3 Two-of-Three Contributors

**Statement**: If `∀ n ∈ {x,y,z}, v n ≤ 1` and `v x + v y + v z ≥ 2`, then `∃ u v ∈ {x,y,z}, u ≠ v ∧ v u ≥ 1 ∧ v v ≥ 1`.

This is pure arithmetic on naturals - no number theory. Avoids the 3-way case split.

### 2.4 Zero-Friendly padicValNat_mul3

```lean
lemma padicValNat_mul3 (p x y z : ℕ) [Fact (Nat.Prime p)] :
    padicValNat p (x * y * z) = padicValNat p x + padicValNat p y + padicValNat p z ∨
    x * y * z = 0
```

Or use `padicValNat_dvd_iff` which has the built-in "or zero" clause.

---

## Part 3: Avoiding `decide` for Prime Facts

### 3.1 Prime Declarations

Mathlib has: `Nat.prime_two`, `Nat.prime_three`, etc.

For 7, 11, 13: either find them or prove directly:
```lean
theorem prime_seven : Nat.Prime 7 := by
  rw [Nat.prime_def_lt]
  constructor
  · norm_num
  · intro m hm1 hm2
    interval_cases m <;> simp  -- or prove structurally
```

### 3.2 Valuation of Specific Numbers

Instead of `native_decide` for `padicValNat 7 6006 = 1`:

```lean
-- Show 7 ∣ 6006
have h1 : 7 ∣ 6006 := ⟨858, rfl⟩

-- Show 49 ∤ 6006
have h2 : ¬(49 ∣ 6006) := by
  intro ⟨k, hk⟩
  -- 6006 = 49k means k = 122.57..., not an integer
  -- Prove via: 49 * 122 = 5978 < 6006 < 6027 = 49 * 123
  have : 49 * 122 < 6006 := by norm_num
  have : 6006 < 49 * 123 := by norm_num
  omega  -- or structural bound argument

-- Conclude
exact padicValNat.eq_one_of_dvd_of_not_dvd_sq h1 h2
```

Even the bounds can be made structural if you express 6006 = 2 × 3 × 7 × 11 × 13 and reason about coprimality.

---

## Part 4: Proposed File Structure

### Toolkit.lean
Short glue lemmas (5-10 lines each):
- `unique_multiple_in_centered_interval`
- `no_multiple_of_mod_distance`
- `two_of_three_contributors`
- `padicValNat_mul3_or_zero`
- `prime_coprime_product_dvd`

### Structural.lean
The main theorem parameterized by:
- Primes p, q, r
- Window center N
- Window radius d
- Hypotheses: d < pq, d < pr, d < qr, d < r²/2
- The modular distance condition for r²

Proves: no valid triple exists.

### WindowFacts_7_11_13.lean
Only proves:
- N = 6006 is the center
- d = 71 is the radius
- Divisibility: 7 ∣ 6006, 11 ∣ 6006, 13 ∣ 6006
- Bounds: 71 < 77, 71 < 91, 71 < 143, 71 < 84.5
- Modular: 6006 mod 169 = 87, and 87 ∈ (71, 98)

Each fact is a one-liner or uses toolkit lemmas.

### Instance_7_11_13.lean
Combines everything into the final ∃ statement.

---

## Part 5: The Dream Proof Sketch

```lean
theorem abc_counterexample : ∃ a b c start, ... := by
  -- Witnesses
  let p := 7; let q := 11; let r := 13
  let N := p * q * r  -- 1001... wait, 6006 = 6 * 1001 = 2 * 3 * 7 * 11 * 13
  let N := 6 * p * q * r  -- = 6006
  let d := (q * r - 1) / 2  -- = 71

  -- The window is [N - d, N + d] = [5935, 6077]
  use p * q, p * r, q * r, N - d

  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  -- Bounds: 0 < pq < pr < qr
  all_goals { apply prime_product_bounds <;> assumption }

  -- Main theorem
  intro x y z hx hy hz hxy hyz hdiv
  apply no_valid_triple_structural
  · exact unique_multiple_lemma N d (p*q) (by linarith) (by exact dvd_of_pqr)
  · exact unique_multiple_lemma N d (p*r) (by linarith) (by exact dvd_of_pqr)
  · exact unique_multiple_lemma N d (q*r) (by linarith) (by exact dvd_of_pqr)
  · exact no_rsq_lemma N d (r^2) (by linarith) (by modular_distance)
  · exact hdiv
```

All the work is in the toolkit lemmas. The instantiation is clean.

---

## Part 6: Next Steps

1. **Find or prove** `Nat.eq_zero_of_dvd_of_lt` in Mathlib
2. **Build** `unique_multiple_in_centered_interval`
3. **Build** `no_multiple_of_mod_distance`
4. **Refactor** Structural.lean to use these
5. **Test** on the 7,11,13 case
6. **Iterate** until no `decide`/`omega` on concrete bounds

The challenge is real but achievable. The key insight from STRUCTURAL_CORE_2.md is that we need **ergonomic wrapper lemmas** - Mathlib has the building blocks, but not assembled in the right shape.

---

## Appendix: Mathlib File Locations

```
.lake/packages/mathlib/Mathlib/NumberTheory/Padics/PadicVal/Basic.lean
.lake/packages/mathlib/Mathlib/NumberTheory/Padics/PadicVal/Defs.lean
.lake/packages/mathlib/Mathlib/Data/Nat/Prime/Basic.lean
.lake/packages/mathlib/Mathlib/RingTheory/Coprime/Basic.lean
.lake/packages/mathlib/Mathlib/RingTheory/Coprime/Lemmas.lean
.lake/packages/mathlib/Mathlib/Data/Int/CardIntervalMod.lean
.lake/packages/mathlib/Mathlib/Order/Interval/Finset/Nat.lean
.lake/packages/mathlib/Mathlib/NumberTheory/Divisors.lean
.lake/packages/mathlib/Mathlib/Data/Nat/Factors.lean
```
