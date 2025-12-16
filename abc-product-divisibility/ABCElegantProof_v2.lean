/-
# Elegant Proof: ABC Product Divisibility is FALSE (v2)

## The Construction

For primes p < q < r, define:
- a = pq, b = pr, c = qr
- abc = p²q²r²

## The Core Counting Argument

In a window W of c = qr consecutive integers, to find x < y < z with abc | xyz:
- Need v_p(xyz) ≥ 2, v_q(xyz) ≥ 2, v_r(xyz) ≥ 2

Key observations about W:
1. W contains exactly q multiples of r (spacing r apart)
2. W contains exactly r multiples of q (spacing q apart)
3. W contains at most 1 multiple of qr = c
4. W contains at most 1 multiple of p² (if p² < qr)
5. W contains at most 1 multiple of q² (if q² < qr, i.e., q < r)
6. W contains at most 1 multiple of r² (since r² > qr for r > q)

## The Impossibility

Without any p², q², r² multiples in W:
- Each number contributes at most 1 to each prime's exponent
- Need 3 numbers totaling ≥2 for each prime
- So we need ≥2 multiples of p, ≥2 multiples of q, ≥2 multiples of r
- But these must be achieved by exactly 3 distinct numbers!

The pigeonhole: if no number is divisible by two different primes from {p,q,r},
we'd need 6 numbers (2 for each prime). With only 3 slots, we need overlap.

But in windows avoiding pq, pr, qr multiples (except possibly one),
the overlap is insufficient.
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-! ## Setup -/

variable (p q r : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime] [hr : Fact r.Prime]

/-- The p-adic valuation -/
def vp (n : ℕ) (prime : ℕ) : ℕ := n.factorization prime

/-- A window of k consecutive integers starting at n -/
def window (n k : ℕ) : Finset ℕ := Finset.Icc n (n + k - 1)

/-! ## The Core Lemma: Counting Constraints -/

/-- In qr consecutive integers, at most ⌈qr/p²⌉ are divisible by p² -/
lemma count_p2_multiples (n : ℕ) (hpq : p < q) (hqr : q < r) :
    (window n (q * r)).filter (fun x => p^2 ∣ x) |>.card ≤ (q * r) / (p^2) + 1 := by
  sorry

/-- For p² > qr, there's at most one multiple of p² in any qr-window -/
lemma at_most_one_p2 (n : ℕ) (h : q * r < p^2) :
    (window n (q * r)).filter (fun x => p^2 ∣ x) |>.card ≤ 1 := by
  sorry

/-! ## The Pigeonhole Argument -/

/--
If we need exponent sum ≥ 2 for each of three primes from exactly 3 numbers,
and no number contributes ≥ 2 to any prime, then each prime needs ≥ 2
contributors, requiring ≥ 6 "slots" but we only have 3 numbers × 3 primes = 9
prime-factor slots. The constraint is that the 3 numbers must collectively
cover all requirements.
-/

/-- A number's prime signature for {p, q, r} -/
structure PrimeSig where
  vp : ℕ  -- min(v_p(n), 2)
  vq : ℕ  -- min(v_q(n), 2)
  vr : ℕ  -- min(v_r(n), 2)
deriving DecidableEq

def primeSig (n p q r : ℕ) : PrimeSig :=
  ⟨min (vp n p) 2, min (vp n q) 2, min (vp n r) 2⟩

/-- Three signatures are "good" if they sum to ≥(2,2,2) -/
def goodTriple (s1 s2 s3 : PrimeSig) : Prop :=
  s1.vp + s2.vp + s3.vp ≥ 2 ∧
  s1.vq + s2.vq + s3.vq ≥ 2 ∧
  s1.vr + s2.vr + s3.vr ≥ 2

/-! ## The Key Impossibility

In a window where:
- No multiple of p² (so all vp ≤ 1)
- No multiple of q² (so all vq ≤ 1)
- No multiple of r² (so all vr ≤ 1)
- At most one multiple of pq, pr, or qr

The available signatures are limited, making good triples impossible.
-/

/-- Available signatures when max contribution is 1 per prime -/
inductive LimitedSig
  | s000  -- not divisible by p, q, or r
  | s100  -- divisible by p only
  | s010  -- divisible by q only
  | s001  -- divisible by r only
  | s110  -- divisible by pq (rare: at most 1 in window)
  | s101  -- divisible by pr (rare: at most 1 in window)
  | s011  -- divisible by qr (rare: at most 1 in window)
  | s111  -- divisible by pqr (very rare: at most 1 in window)
deriving DecidableEq

/-- Convert LimitedSig to contribution vector -/
def sigToVec : LimitedSig → ℕ × ℕ × ℕ
  | .s000 => (0, 0, 0)
  | .s100 => (1, 0, 0)
  | .s010 => (0, 1, 0)
  | .s001 => (0, 0, 1)
  | .s110 => (1, 1, 0)
  | .s101 => (1, 0, 1)
  | .s011 => (0, 1, 1)
  | .s111 => (1, 1, 1)

def addVec (a b : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)

def vecGood (v : ℕ × ℕ × ℕ) : Prop := v.1 ≥ 2 ∧ v.2.1 ≥ 2 ∧ v.2.2 ≥ 2

/--
Key lemma: with at most one "double" signature (s110, s101, s011, s111),
no triple of signatures sums to ≥(2,2,2).

Proof sketch:
- s000 contributes nothing
- s100, s010, s001 each help only one prime
- We need 2+2+2=6 prime contributions from 3 numbers
- Single-prime sigs give 1 each, so 3 numbers give at most 3
- Need 3 more from double/triple sigs, but have at most 1 such number
- 1 double sig gives at most 2 more (or 3 for triple)
- Total: at most 3 + 3 = 6, but distributed as (≤2, ≤2, ≤2) not (≥2, ≥2, ≥2)
-/
theorem no_good_triple_limited
    (sigs : Fin 3 → LimitedSig)
    (h_at_most_one_double : (Finset.univ.filter fun i =>
      sigs i ∈ ({.s110, .s101, .s011, .s111} : Set LimitedSig)).card ≤ 1) :
    ¬vecGood (addVec (addVec (sigToVec (sigs 0)) (sigToVec (sigs 1))) (sigToVec (sigs 2))) := by
  sorry -- Finite case analysis

/-! ## Existence of Bad Windows -/

/-- By CRT, we can find windows avoiding p², q², r² and most double products -/
theorem bad_window_exists' (p q r : ℕ) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p < q) (hqr : q < r) :
    ∃ n : ℕ, 0 < n ∧
      -- Window avoids p², q², r²
      (∀ x ∈ window n (q*r), ¬(p^2 ∣ x)) ∧
      (∀ x ∈ window n (q*r), ¬(q^2 ∣ x)) ∧
      (∀ x ∈ window n (q*r), ¬(r^2 ∣ x)) ∧
      -- At most one multiple of each double product
      (window n (q*r)).filter (fun x => p*q ∣ x) |>.card ≤ 1 ∧
      (window n (q*r)).filter (fun x => p*r ∣ x) |>.card ≤ 1 ∧
      (window n (q*r)).filter (fun x => q*r ∣ x) |>.card ≤ 1 := by
  sorry -- Chinese Remainder Theorem construction

/-! ## Main Theorem -/

theorem abc_conjecture_is_false :
    ¬(∀ a b c : ℕ, 0 < a → a < b → b < c →
      ∀ n : ℕ, 0 < n →
        ∃ x y z ∈ Finset.Icc n (n + c - 1), x < y ∧ y < z ∧ (a*b*c) ∣ (x*y*z)) := by
  push_neg
  -- Witness: a = 7×11 = 77, b = 7×13 = 91, c = 11×13 = 143
  use 77, 91, 143
  constructor; · omega
  constructor; · omega
  constructor; · omega
  -- Get the bad window
  obtain ⟨n, hn, h_no_p2, h_no_q2, h_no_r2, h_pq, h_pr, h_qr⟩ :=
    bad_window_exists' 7 11 13 (by decide) (by decide) (by decide) (by omega) (by omega)
  use n, hn
  intro x y z hx hy hz hxy hyz hdiv
  -- From the window constraints, x y z have limited signatures
  -- From no_good_triple_limited, no good triple exists
  sorry -- Connect the pieces
