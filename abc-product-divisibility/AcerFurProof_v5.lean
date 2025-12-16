/-
# AcerFur's Proof v5: Computational + Structural

Strategy: prove the "sum ≤ 5" bound computationally using native_decide,
then use padicValNat lemmas for the "need ≥ 6" part.
-/

import Mathlib.NumberTheory.Padics.PadicVal.Basic

instance : Fact (Nat.Prime 7) := ⟨by decide⟩
instance : Fact (Nat.Prime 11) := ⟨by decide⟩
instance : Fact (Nat.Prime 13) := ⟨by decide⟩

def windowStart : ℕ := 5935
def windowEnd : ℕ := 6077

abbrev vp (n : ℕ) := padicValNat 7 n
abbrev vq (n : ℕ) := padicValNat 11 n
abbrev vr (n : ℕ) := padicValNat 13 n

/-- Total valuation sum for a number -/
def valSum (n : ℕ) : ℕ := vp n + vq n + vr n

/-! ## Computational Bounds -/

/-- Check that for all x in [5935, 6077] with x ≠ 6006, valSum x ≤ 1 -/
def checkNon6006Bound : Bool :=
  (List.range (windowEnd - windowStart + 1)).all fun i =>
    let x := windowStart + i
    x = 6006 ∨ valSum x ≤ 1

theorem non6006_bound_check : checkNon6006Bound = true := by native_decide

/-- Check that valSum 6006 = 3 -/
theorem valSum_6006 : valSum 6006 = 3 := by native_decide

/-- For non-6006 in window, valSum ≤ 1 -/
theorem valSum_le_one_of_ne_6006 (x : ℕ)
    (hlo : windowStart ≤ x) (hhi : x ≤ windowEnd) (hne : x ≠ 6006) :
    valSum x ≤ 1 := by
  have h := non6006_bound_check
  simp only [checkNon6006Bound, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  have hx : x - windowStart < windowEnd - windowStart + 1 := by omega
  specialize h (x - windowStart) hx
  simp only [windowStart] at h
  have heq : 5935 + (x - 5935) = x := by omega
  rw [heq] at h
  cases h with
  | inl h => exact absurd h hne
  | inr h => exact h

/-! ## The Main Bound -/

theorem total_valSum_le_5 (x y z : ℕ)
    (hx : windowStart ≤ x ∧ x ≤ windowEnd)
    (hy : windowStart ≤ y ∧ y ≤ windowEnd)
    (hz : windowStart ≤ z ∧ z ≤ windowEnd)
    (hxy : x < y) (hyz : y < z) :
    valSum x + valSum y + valSum z ≤ 5 := by
  -- At most one of x, y, z can be 6006
  by_cases hx6 : x = 6006
  · have hy6 : y ≠ 6006 := by omega
    have hz6 : z ≠ 6006 := by omega
    have hbx := valSum_6006
    have hby := valSum_le_one_of_ne_6006 y hy.1 hy.2 hy6
    have hbz := valSum_le_one_of_ne_6006 z hz.1 hz.2 hz6
    omega
  · by_cases hy6 : y = 6006
    · have hz6 : z ≠ 6006 := by omega
      have hbx := valSum_le_one_of_ne_6006 x hx.1 hx.2 hx6
      have hby := valSum_6006
      have hbz := valSum_le_one_of_ne_6006 z hz.1 hz.2 hz6
      omega
    · by_cases hz6 : z = 6006
      · have hbx := valSum_le_one_of_ne_6006 x hx.1 hx.2 hx6
        have hby := valSum_le_one_of_ne_6006 y hy.1 hy.2 hy6
        have hbz := valSum_6006
        omega
      · have hbx := valSum_le_one_of_ne_6006 x hx.1 hx.2 hx6
        have hby := valSum_le_one_of_ne_6006 y hy.1 hy.2 hy6
        have hbz := valSum_le_one_of_ne_6006 z hz.1 hz.2 hz6
        omega

/-! ## The Divisibility Requirement -/

theorem need_valSum_ge_6 (x y z : ℕ) (hxyz : x * y * z ≠ 0)
    (hdiv : 7^2 * 11^2 * 13^2 ∣ x * y * z) :
    valSum x + valSum y + valSum z ≥ 6 := by
  have hx : x ≠ 0 := by intro h; simp [h] at hxyz
  have hy : y ≠ 0 := by intro h; simp [h] at hxyz
  have hz : z ≠ 0 := by intro h; simp [h] at hxyz
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy

  -- Extract divisibility
  have h7 : 7^2 ∣ x * y * z := by
    have : 7^2 * 11^2 * 13^2 = 7^2 * (11^2 * 13^2) := by ring
    rw [this] at hdiv
    exact Nat.dvd_of_mul_dvd_mul_right (by decide : 0 < 11^2 * 13^2) hdiv
  have h11 : 11^2 ∣ x * y * z := by
    have : 7^2 * 11^2 * 13^2 = 11^2 * (7^2 * 13^2) := by ring
    rw [this] at hdiv
    exact Nat.dvd_of_mul_dvd_mul_right (by decide : 0 < 7^2 * 13^2) hdiv
  have h13 : 13^2 ∣ x * y * z := by
    have : 7^2 * 11^2 * 13^2 = 13^2 * (7^2 * 11^2) := by ring
    rw [this] at hdiv
    exact Nat.dvd_of_mul_dvd_mul_right (by decide : 0 < 7^2 * 11^2) hdiv

  -- Convert to valuation inequalities
  have hv7 : vp (x * y * z) ≥ 2 := padicValNat_dvd_iff_le hxyz |>.mp h7
  have hv11 : vq (x * y * z) ≥ 2 := padicValNat_dvd_iff_le hxyz |>.mp h11
  have hv13 : vr (x * y * z) ≥ 2 := padicValNat_dvd_iff_le hxyz |>.mp h13

  -- Expand valuations of product
  have hvp : vp (x * y * z) = vp x + vp y + vp z := by
    rw [padicValNat.mul hxy hz, padicValNat.mul hx hy]
  have hvq : vq (x * y * z) = vq x + vq y + vq z := by
    rw [padicValNat.mul hxy hz, padicValNat.mul hx hy]
  have hvr : vr (x * y * z) = vr x + vr y + vr z := by
    rw [padicValNat.mul hxy hz, padicValNat.mul hx hy]

  -- Combine
  simp only [valSum]
  rw [hvp] at hv7; rw [hvq] at hv11; rw [hvr] at hv13
  omega

/-! ## Main Theorem -/

theorem no_valid_triple (x y z : ℕ)
    (hx : windowStart ≤ x ∧ x ≤ windowEnd)
    (hy : windowStart ≤ y ∧ y ≤ windowEnd)
    (hz : windowStart ≤ z ∧ z ≤ windowEnd)
    (hxy : x < y) (hyz : y < z)
    (hdiv : 7^2 * 11^2 * 13^2 ∣ x * y * z) : False := by
  have hxyz : x * y * z ≠ 0 := by
    simp only [windowStart] at hx hy hz
    omega
  have hbound := total_valSum_le_5 x y z hx hy hz hxy hyz
  have hneed := need_valSum_ge_6 x y z hxyz hdiv
  omega

/-- ABC conjecture is false -/
theorem abc_conjecture_is_false :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧
      ∃ start : ℕ, 0 < start ∧
        ∀ x y z, start ≤ x → x ≤ start + c - 1 →
                 start ≤ y → y ≤ start + c - 1 →
                 start ≤ z → z ≤ start + c - 1 →
                 x < y → y < z → ¬(a * b * c ∣ x * y * z) := by
  use 77, 91, 143
  refine ⟨by decide, by decide, by decide, windowStart, by decide, ?_⟩
  intro x y z hxlo hxhi hylo hyhi hzlo hzhi hxy hyz hdiv
  have hend : windowStart + 143 - 1 = windowEnd := by decide
  rw [hend] at hxhi hyhi hzhi
  have habc : 77 * 91 * 143 = 7^2 * 11^2 * 13^2 := by decide
  rw [habc] at hdiv
  exact no_valid_triple x y z ⟨hxlo, hxhi⟩ ⟨hylo, hyhi⟩ ⟨hzlo, hzhi⟩ hxy hyz hdiv
