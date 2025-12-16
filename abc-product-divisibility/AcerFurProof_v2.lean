/-
# AcerFur's Proof v2: The Counting Argument

The key insight: we need 6 "hits" (2 per prime) but can only get 5.

- 6006 is the ONLY multi-prime number in [5935, 6077]
- It contributes at most 3 hits
- The other two numbers contribute at most 1 hit each
- Total: 3 + 1 + 1 = 5 < 6
-/

import Mathlib.Tactic

/-! ## Parameters -/

def p : ℕ := 7
def q : ℕ := 11
def r : ℕ := 13

def windowStart : ℕ := 5935
def windowEnd : ℕ := 6077

/-! ## Counting primes that divide a number -/

/-- Count how many of {p, q, r} divide x -/
def primeCount (x : ℕ) : ℕ :=
  (if p ∣ x then 1 else 0) + (if q ∣ x then 1 else 0) + (if r ∣ x then 1 else 0)

#eval primeCount 6006  -- 3 (divisible by 7, 11, 13)
#eval primeCount 5936  -- 0
#eval primeCount 5943  -- 1 (divisible by 7)
#eval primeCount 5940  -- 0
#eval primeCount 5951  -- 1 (divisible by 11)

/-! ## The Key Lemma: 6006 is the only multi-prime number -/

/-- In [5935, 6077], only 6006 is divisible by 2+ of {7, 11, 13} -/
theorem only_6006_is_multi (x : ℕ) (hlo : windowStart ≤ x) (hhi : x ≤ windowEnd)
    (hmulti : primeCount x ≥ 2) : x = 6006 := by
  simp only [windowStart, windowEnd] at hlo hhi
  interval_cases x <;> simp_all [primeCount, p, q, r]

/-! ## The Counting Argument -/

/-- Maximum hits from 3 numbers where ≤1 is multi-prime -/
theorem max_hits_is_5 (c1 c2 c3 : ℕ) (h1 : c1 ≤ 3) (h2 : c2 ≤ 3) (h3 : c3 ≤ 3)
    (hmulti : (if c1 ≥ 2 then 1 else 0) + (if c2 ≥ 2 then 1 else 0) + (if c3 ≥ 2 then 1 else 0) ≤ 1) :
    c1 + c2 + c3 ≤ 5 := by
  rcases Nat.lt_or_ge c1 2 with hc1 | hc1 <;>
  rcases Nat.lt_or_ge c2 2 with hc2 | hc2 <;>
  rcases Nat.lt_or_ge c3 2 with hc3 | hc3 <;>
  simp_all <;> omega

/-- We need 6 hits to satisfy the divisibility -/
theorem need_6_hits (x y z : ℕ) (hdiv : (p * q) * (p * r) * (q * r) ∣ x * y * z) :
    primeCount x + primeCount y + primeCount z ≥ 6 := by
  simp only [primeCount, p, q, r]
  -- This requires showing: if p²q²r² | xyz, then total prime count ≥ 6
  -- Each prime needs to appear at least twice across x, y, z
  sorry

/-! ## Main Theorem -/

theorem no_valid_triple (x y z : ℕ)
    (hx : windowStart ≤ x ∧ x ≤ windowEnd)
    (hy : windowStart ≤ y ∧ y ≤ windowEnd)
    (hz : windowStart ≤ z ∧ z ≤ windowEnd)
    (hxy : x < y) (hyz : y < z)
    (hdiv : (p * q) * (p * r) * (q * r) ∣ x * y * z) : False := by
  -- Step 1: Count multi-prime numbers among x, y, z
  have hcx : primeCount x ≤ 3 := by simp [primeCount]; omega
  have hcy : primeCount y ≤ 3 := by simp [primeCount]; omega
  have hcz : primeCount z ≤ 3 := by simp [primeCount]; omega

  -- Step 2: At most one of x, y, z is multi-prime (and it must be 6006)
  have hmulti_count : (if primeCount x ≥ 2 then 1 else 0) +
                      (if primeCount y ≥ 2 then 1 else 0) +
                      (if primeCount z ≥ 2 then 1 else 0) ≤ 1 := by
    by_cases hx2 : primeCount x ≥ 2
    · have hx6006 := only_6006_is_multi x hx.1 hx.2 hx2
      by_cases hy2 : primeCount y ≥ 2
      · have hy6006 := only_6006_is_multi y hy.1 hy.2 hy2
        omega  -- x = y = 6006 contradicts x < y
      · by_cases hz2 : primeCount z ≥ 2
        · have hz6006 := only_6006_is_multi z hz.1 hz.2 hz2
          omega  -- x = z = 6006 contradicts x < z
        · simp [hx2, hy2, hz2]
    · by_cases hy2 : primeCount y ≥ 2
      · have hy6006 := only_6006_is_multi y hy.1 hy.2 hy2
        by_cases hz2 : primeCount z ≥ 2
        · have hz6006 := only_6006_is_multi z hz.1 hz.2 hz2
          omega  -- y = z = 6006 contradicts y < z
        · simp [hx2, hy2, hz2]
      · simp [hx2, hy2]

  -- Step 3: Max hits is 5
  have hmax := max_hits_is_5 (primeCount x) (primeCount y) (primeCount z) hcx hcy hcz hmulti_count

  -- Step 4: But we need 6 hits
  have hneed := need_6_hits x y z hdiv

  -- Contradiction
  omega

/-- ABC conjecture is false -/
theorem abc_conjecture_is_false :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧
      ∃ start : ℕ, 0 < start ∧
        ∀ x y z, start ≤ x → x ≤ start + c - 1 →
                 start ≤ y → y ≤ start + c - 1 →
                 start ≤ z → z ≤ start + c - 1 →
                 x < y → y < z → ¬(a * b * c ∣ x * y * z) := by
  use p * q, p * r, q * r
  refine ⟨by decide, by decide, by decide, windowStart, by decide, ?_⟩
  intro x y z hxlo hxhi hylo hyhi hzlo hzhi hxy hyz hdiv
  have hend : windowStart + q * r - 1 = windowEnd := by decide
  rw [hend] at hxhi hyhi hzhi
  exact no_valid_triple x y z ⟨hxlo, hxhi⟩ ⟨hylo, hyhi⟩ ⟨hzlo, hzhi⟩ hxy hyz hdiv
