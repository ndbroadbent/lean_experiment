# ABC Product Divisibility Project

## Goal

Prove the ABC product divisibility conjecture is **FALSE** using **purely structural reasoning** — no concrete numbers, no `decide`, no `native_decide`.

The proof should demonstrate WHY the conjecture fails, not just THAT it fails.

## The Conjecture

For positive integers a < b < c, does there always exist x, y, z with:
- start ≤ x < y < z < start + c (consecutive in a window of width c)
- a²b²c² | xyz

**Answer**: NO — and the failure is structural, not accidental.

## Key Insight

For primes p < q < r with **r < 2p**, the conjecture fails because:

1. The window centered at N = pqr with radius d = (qr-1)/2 has width < qr
2. Since r < 2p, we have d < pq, d < pr, d < qr — so each product has a **unique multiple** (which is N)
3. Since q < r, we have qr < r², so **no r² multiple** exists in the window
4. The divisibility requirement p²q²r² | xyz needs:
   - Two numbers divisible by r (to get r² total, since no single number has r²)
   - But only one r-multiple (N) can also have p or q
   - The "pure r" number contributes nothing to p² and q²
   - The third number must carry all of p² and q² — impossible since it equals N (which has single copies)

This is a **pigeonhole impossibility** — the constraints are inherently incompatible.

## File Structure

- **Structural.lean**: Generic proof that WindowProps A/B/C/D imply no valid triple exists
- **AbstractImpossibility.lean**: Attempts to prove WindowProps hold for any primes with r < 2p
- **AcerFurProof_v7.lean**: Working concrete proof using native_decide (for reference)
- **MATHLIB.md**: Reference for key Mathlib lemmas

## Key Mathlib Lemmas

From MATHLIB.md:

```lean
-- Valuation of product
padicValNat.mul : a ≠ 0 → b ≠ 0 → padicValNat p (a * b) = padicValNat p a + padicValNat p b

-- Divisibility ↔ valuation
padicValNat_dvd_iff_le [Fact p.Prime] (ha : a ≠ 0) : p ^ n ∣ a ↔ n ≤ padicValNat p a

-- Valuation of different prime
padicValNat_primes [Fact p.Prime] [Fact q.Prime] (neq : p ≠ q) : padicValNat p q = 0

-- Coprimality of distinct primes
coprime_primes (pp : Prime p) (pq : Prime q) : Coprime p q ↔ p ≠ q
```

## The Structural Approach

### Step 1: `unique_multiple_centered`
If m | N and d < m, then N is the unique m-multiple in [N-d, N+d].
**Proof**: Any other multiple differs from N by a nonzero amount < m, which can't be divisible by m.

### Step 2: Inequalities from r < 2p
- d = (qr-1)/2 < pq (because r < 2p)
- d < pr (because q < r < 2p)
- d < qr (trivially)

### Step 3: No r² in window — **PROBLEMATIC**
**ISSUE DISCOVERED**: The claim "N = pqr centered window has no r² multiple" is **FALSE**.

For (7, 11, 13):
- N = pqr = 1001
- d = (143-1)/2 = 71
- Window = [930, 1072]
- 169-multiples: 845, 1014, 1183
- 1014 is IN the window [930, 1072]!

The concrete proof (AcerFurProof_v7.lean) uses a **different center point**: 6006 = 6 * pqr, not pqr.
For that window [5935, 6077]:
- 169-multiples: 5915, 6084
- Neither is in the window — it works!

**Conclusion**: The abstract approach with N = pqr doesn't work directly. We need to find the
right center point for each prime triple, which requires a more sophisticated analysis.

### Step 4: Property D (N has single copies)
- padicValNat p (pqr) = 1 (since q, r are different primes)
- Similarly for q and r
- Therefore p² ∤ N, q² ∤ N, r² ∤ N

### Step 5: Apply `no_valid_triple_of_window_props`
The generic theorem in Structural.lean handles the pigeonhole argument.

## Current Status

- [x] Structural.lean: Generic proof complete (no sorry)
- [ ] AbstractImpossibility.lean: Has fundamental issue (1 sorry remaining)
  - [x] `unique_multiple_centered` lemma - PROVEN
  - [x] `padicValNat_pqr` and `sq_not_dvd_pqr` - PROVEN
  - [x] `half_sub_one_lt` helper - PROVEN
  - [x] `radius_lt_pq`, `radius_lt_pr`, `radius_lt_qr` - PROVEN
  - [x] `radius_le_N`, divisibility lemmas - PROVEN
  - [x] `qr_odd` and `p_ge_three` - PROVEN
  - [ ] `no_r_squared_in_window` — **LEMMA IS FALSE** for N = pqr center
  - [x] `abc_impossible_abstract` - PROVEN (depends on the false lemma)
- [x] AcerFurProof_v7.lean: Working concrete proof (uses native_decide)

## Why This Matters

The proof shows the conjecture fails for an **infinite family** of prime triples:
- (7, 11, 13): 13 < 14 ✓
- (11, 13, 17): 17 < 22 ✓
- (13, 17, 19): 19 < 26 ✓
- ... infinitely more

This is not "here's a counterexample" — it's "the constraints are **impossible by definition**."

## Build Commands

```bash
lake build Structural
lake build AbstractImpossibility  # Warning: has sorry
lake build AcerFurProof_v7        # Complete concrete proof
```

## Fundamental Issue

The abstract approach assumes we can center the window at N = pqr. However, this doesn't
guarantee no r²-multiple in the window. The working concrete proof uses a different center.

To fix the abstract proof, we would need to:

1. **Find the right center**: For each prime triple, find a point N' such that:
   - pq | N', pr | N', qr | N'
   - N' mod r² is "far from 0 and r²" (distance > d)

2. **Prove such N' exists**: Show that for any primes p < q < r with r < 2p, there exists
   a suitable center point.

This is more complex than the original approach and may require number-theoretic lemmas
about the distribution of residues.

## Alternative Approaches

1. **Multiple centers**: Show that among several candidates (pqr, 2pqr, ..., 6pqr), at least
   one has no r²-multiple in its window.

2. **Different window definition**: Use a different window structure that doesn't require
   "no r² in window".

3. **Accept partial result**: The current code proves the result assuming the (false)
   no_r_squared lemma. If we could find the right center, the rest of the proof works.
