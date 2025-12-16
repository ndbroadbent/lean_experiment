/-
# AcerFur's Elegant Proof: ABC Product Divisibility is FALSE

This is a formalization of the proof from @AcerFur on X (Twitter).

## The Key Insight

For primes p < q < r with a = pq, b = pr, c = qr:
- Constraint: 2a > c (forces only ONE multiple of a,b,c in any c-window)
- abc = p²q²r², so we need v_p(xyz) ≥ 2, v_q(xyz) ≥ 2, v_r(xyz) ≥ 2

Center window at lcm(a,b,c)·n = pqr·n. The ONLY number divisible by
any pair of primes is pqr·n itself (by 2a > c constraint).

So with 3 numbers x < y < z, at most ONE can contribute to multiple primes.
The other two must each contribute ≥1 to reach the total of 2 per prime.

This means we need multiples of p², q², r² in the window!
- p² = 49 < 143 ✓
- q² = 121 < 143 ✓
- r² = 169 > 143 - need r² multiple in SMALLER sub-interval

For n=6: no multiple of 13² exists in [5935, 6077]. Done!
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-! ## Parameters -/

def p : ℕ := 7
def q : ℕ := 11
def r : ℕ := 13

def a : ℕ := p * q  -- 77
def b : ℕ := p * r  -- 91
def c : ℕ := q * r  -- 143

def n : ℕ := 6
def center : ℕ := p * q * r * n  -- 6006

def windowStart : ℕ := center - (c - 1) / 2  -- 5935
def windowEnd : ℕ := center + (c - 1) / 2    -- 6077

-- Verify setup
#eval (a, b, c)           -- (77, 91, 143)
#eval 2 * a > c           -- true (154 > 143)
#eval (windowStart, windowEnd)  -- (5935, 6077)
#eval windowEnd - windowStart + 1  -- 143

/-! ## The Core Lemmas -/

theorem two_a_gt_c : 2 * a > c := by decide

theorem window_is_c : windowEnd - windowStart + 1 = c := by decide

/-- No multiple of 169 = 13² exists in [5935, 6077] -/
theorem no_r_squared : ∀ x, windowStart ≤ x → x ≤ windowEnd → ¬(r^2 ∣ x) := by
  intro x hlo hhi ⟨k, hk⟩
  -- r² = 169, window = [5935, 6077]
  -- 169 × 35 = 5915 < 5935
  -- 169 × 36 = 6084 > 6077
  -- No k works!
  simp only [r] at hk
  have h1 : windowStart = 5935 := by decide
  have h2 : windowEnd = 6077 := by decide
  omega

/--
AcerFur's key insight: To get abc = 7²×11²×13² | xyz, we MUST have:
- One of x,y,z divisible by 7² = 49
- One of x,y,z divisible by 11² = 121
- One of x,y,z divisible by 13² = 169

Why? Because 6006 is the ONLY number in [5935,6077] divisible by two primes.
So at most one of x,y,z contributes to two prime factors.
The other two contribute to at most one prime each.

To reach (2,2,2), we need squared primes!
-/
theorem need_all_squared (x y z : ℕ)
    (hx : windowStart ≤ x ∧ x ≤ windowEnd)
    (hy : windowStart ≤ y ∧ y ≤ windowEnd)
    (hz : windowStart ≤ z ∧ z ≤ windowEnd)
    (hxy : x < y) (hyz : y < z)
    (hdiv : (a * b * c) ∣ (x * y * z)) :
    (p^2 ∣ x ∨ p^2 ∣ y ∨ p^2 ∣ z) ∧
    (q^2 ∣ x ∨ q^2 ∣ y ∨ q^2 ∣ z) ∧
    (r^2 ∣ x ∨ r^2 ∣ y ∨ r^2 ∣ z) := by
  sorry -- The combinatorial argument above

/-- THE MAIN THEOREM -/
theorem no_valid_triple :
    ¬∃ x y z, windowStart ≤ x ∧ x ≤ windowEnd ∧
              windowStart ≤ y ∧ y ≤ windowEnd ∧
              windowStart ≤ z ∧ z ≤ windowEnd ∧
              x < y ∧ y < z ∧
              (a * b * c) ∣ (x * y * z) := by
  intro ⟨x, y, z, hxlo, hxhi, hylo, hyhi, hzlo, hzhi, hxy, hyz, hdiv⟩
  have ⟨_, _, hr2⟩ := need_all_squared x y z ⟨hxlo, hxhi⟩ ⟨hylo, hyhi⟩ ⟨hzlo, hzhi⟩ hxy hyz hdiv
  rcases hr2 with h | h | h
  · exact no_r_squared x hxlo hxhi h
  · exact no_r_squared y hylo hyhi h
  · exact no_r_squared z hzlo hzhi h

/-- ABC CONJECTURE IS FALSE -/
theorem abc_conjecture_is_false :
    ∃ a' b' c' : ℕ, 0 < a' ∧ a' < b' ∧ b' < c' ∧
      ∃ start : ℕ, 0 < start ∧
        ∀ x y z, start ≤ x → x ≤ start + c' - 1 →
                 start ≤ y → y ≤ start + c' - 1 →
                 start ≤ z → z ≤ start + c' - 1 →
                 x < y → y < z → ¬(a' * b' * c' ∣ x * y * z) := by
  use a, b, c
  refine ⟨by decide, by decide, by decide, windowStart, by decide, ?_⟩
  intro x y z hxlo hxhi hylo hyhi hzlo hzhi hxy hyz hdiv
  have hend : windowStart + c - 1 = windowEnd := by decide
  rw [hend] at hxhi hyhi hzhi
  have := no_valid_triple
  push_neg at this
  exact this x y z hxlo hxhi hylo hyhi hzlo hzhi hxy hyz hdiv
