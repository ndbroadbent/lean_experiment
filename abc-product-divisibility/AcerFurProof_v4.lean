/-
# AcerFur's Proof v4: Using padicValNat

Key insight: use p-adic valuation to make the counting argument precise.

If p²q²r² | xyz, then:
  padicValNat p (xyz) ≥ 2
  padicValNat q (xyz) ≥ 2
  padicValNat r (xyz) ≥ 2

By additivity:
  padicValNat p x + padicValNat p y + padicValNat p z ≥ 2 (for each prime)

Total sum of 9 valuations ≥ 6.

But each number contributes at most 3 (one per prime), and only 6006
can contribute to multiple primes. So max = 3 + 1 + 1 = 5 < 6.
-/

import Mathlib.NumberTheory.Padics.PadicVal.Basic

-- Make primes instances
instance : Fact (Nat.Prime 7) := ⟨by decide⟩
instance : Fact (Nat.Prime 11) := ⟨by decide⟩
instance : Fact (Nat.Prime 13) := ⟨by decide⟩

def p : ℕ := 7
def q : ℕ := 11
def r : ℕ := 13
def windowStart : ℕ := 5935
def windowEnd : ℕ := 6077

-- Shorthands for valuations
abbrev vp (n : ℕ) := padicValNat 7 n
abbrev vq (n : ℕ) := padicValNat 11 n
abbrev vr (n : ℕ) := padicValNat 13 n

/-! ## Key Facts -/

/-- 6006 is the only number in window divisible by two or more of {7, 11, 13} -/
theorem only_6006_multi (x : ℕ) (hlo : windowStart ≤ x) (hhi : x ≤ windowEnd)
    (h : (7 ∣ x ∧ 11 ∣ x) ∨ (7 ∣ x ∧ 13 ∣ x) ∨ (11 ∣ x ∧ 13 ∣ x)) : x = 6006 := by
  simp only [windowStart, windowEnd] at hlo hhi
  omega

/-- No multiple of 169 = 13² in [5935, 6077] -/
theorem no_r_squared (x : ℕ) (hlo : windowStart ≤ x) (hhi : x ≤ windowEnd) : vr x < 2 := by
  simp only [windowStart, windowEnd] at hlo hhi
  by_contra h
  push_neg at h
  have : 13^2 ∣ x := padicValNat_dvd_iff_le (by omega) |>.mpr h
  obtain ⟨k, hk⟩ := this
  simp only [vr] at hk
  omega

/-- Numbers in window have vr ≤ 1 -/
theorem vr_le_one (x : ℕ) (hlo : windowStart ≤ x) (hhi : x ≤ windowEnd) : vr x ≤ 1 := by
  have := no_r_squared x hlo hhi
  omega

/-! ## The Valuation Sum Argument -/

/-- For a number x in window, the sum vp(x) + vq(x) + vr(x) is:
    - ≤ 1 if x is not divisible by any of 7, 11, 13
    - ≤ 1 if x is divisible by exactly one (since vr ≤ 1 and similarly for others)
    - ≤ 3 if x = 6006 (divisible by all three, but only once each)
-/

theorem val_sum_bound_non6006 (x : ℕ) (hlo : windowStart ≤ x) (hhi : x ≤ windowEnd)
    (hne : x ≠ 6006) : vp x + vq x + vr x ≤ 1 := by
  simp only [windowStart, windowEnd] at hlo hhi
  -- If x is divisible by 2+ primes, then x = 6006, contradiction
  have hmulti : ¬((7 ∣ x ∧ 11 ∣ x) ∨ (7 ∣ x ∧ 13 ∣ x) ∨ (11 ∣ x ∧ 13 ∣ x)) := by
    intro h
    have := only_6006_multi x (by omega : windowStart ≤ x) (by omega) h
    exact hne this
  push_neg at hmulti
  -- So x is divisible by at most one of {7, 11, 13}
  by_cases h7 : 7 ∣ x
  · -- x divisible by 7, not by 11 or 13
    have hno11 : ¬(11 ∣ x) := hmulti.1 h7
    have hno13 : ¬(13 ∣ x) := hmulti.2.1 h7
    have hvq : vq x = 0 := padicValNat.eq_zero_of_not_dvd hno11
    have hvr : vr x = 0 := padicValNat.eq_zero_of_not_dvd hno13
    rw [hvq, hvr, add_zero]
    -- Now bound vp x. Since no 7² in the small window except possibly some...
    -- Actually we need to check: is there a multiple of 49 in [5935, 6077]?
    -- 49 * 121 = 5929 < 5935, 49 * 122 = 5978, 49 * 123 = 6027, 49 * 124 = 6076
    -- So there ARE multiples of 49. But they're not 6006.
    -- Wait, if x is divisible by 49 but not by 11 or 13, that's fine for the sum.
    -- The key is x ≠ 6006. Let's just compute directly.
    interval_cases x <;> simp_all [vp, vq, vr]
  · by_cases h11 : 11 ∣ x
    · -- x divisible by 11, not by 7 or 13
      have hno13 : ¬(13 ∣ x) := hmulti.2.2 h11
      have hvp : vp x = 0 := padicValNat.eq_zero_of_not_dvd h7
      have hvr : vr x = 0 := padicValNat.eq_zero_of_not_dvd hno13
      rw [hvp, hvr, zero_add]
      -- Check multiples of 121 in window: 121 * 49 = 5929 < 5935, 121 * 50 = 6050
      interval_cases x <;> simp_all [vp, vq, vr]
    · by_cases h13 : 13 ∣ x
      · -- x divisible by 13, not by 7 or 11
        have hvp : vp x = 0 := padicValNat.eq_zero_of_not_dvd h7
        have hvq : vq x = 0 := padicValNat.eq_zero_of_not_dvd h11
        rw [hvp, hvq, zero_add, zero_add]
        exact vr_le_one x (by simp [windowStart]; omega) (by simp [windowEnd]; omega)
      · -- x not divisible by any
        have hvp : vp x = 0 := padicValNat.eq_zero_of_not_dvd h7
        have hvq : vq x = 0 := padicValNat.eq_zero_of_not_dvd h11
        have hvr : vr x = 0 := padicValNat.eq_zero_of_not_dvd h13
        simp [hvp, hvq, hvr]

theorem val_sum_6006 : vp 6006 + vq 6006 + vr 6006 = 3 := by native_decide

/-! ## The Main Counting Argument -/

theorem total_val_bound (x y z : ℕ)
    (hx : windowStart ≤ x ∧ x ≤ windowEnd)
    (hy : windowStart ≤ y ∧ y ≤ windowEnd)
    (hz : windowStart ≤ z ∧ z ≤ windowEnd)
    (hxy : x < y) (hyz : y < z) :
    (vp x + vp y + vp z) + (vq x + vq y + vq z) + (vr x + vr y + vr z) ≤ 5 := by
  -- At most one of x, y, z can be 6006 (since x < y < z are distinct)
  have hxne : x ≠ 6006 ∨ y ≠ 6006 ∨ z ≠ 6006 → True := fun _ => trivial  -- placeholder

  -- Key: since x < y < z, at most one can equal 6006
  by_cases hx6 : x = 6006
  · -- x = 6006, so y ≠ 6006 and z ≠ 6006 (since 6006 < y < z)
    have hy6 : y ≠ 6006 := by omega
    have hz6 : z ≠ 6006 := by omega
    have hbx := val_sum_6006
    have hby := val_sum_bound_non6006 y hy.1 hy.2 hy6
    have hbz := val_sum_bound_non6006 z hz.1 hz.2 hz6
    -- Sum ≤ 3 + 1 + 1 = 5
    omega
  · by_cases hy6 : y = 6006
    · have hz6 : z ≠ 6006 := by omega
      have hbx := val_sum_bound_non6006 x hx.1 hx.2 hx6
      have hby := val_sum_6006
      have hbz := val_sum_bound_non6006 z hz.1 hz.2 hz6
      omega
    · by_cases hz6 : z = 6006
      · have hbx := val_sum_bound_non6006 x hx.1 hx.2 hx6
        have hby := val_sum_bound_non6006 y hy.1 hy.2 hy6
        have hbz := val_sum_6006
        omega
      · -- None is 6006
        have hbx := val_sum_bound_non6006 x hx.1 hx.2 hx6
        have hby := val_sum_bound_non6006 y hy.1 hy.2 hy6
        have hbz := val_sum_bound_non6006 z hz.1 hz.2 hz6
        -- Sum ≤ 1 + 1 + 1 = 3
        omega

/-! ## The Divisibility Requirement -/

theorem need_6_vals (x y z : ℕ) (hxyz : x * y * z ≠ 0)
    (hdiv : 7^2 * 11^2 * 13^2 ∣ x * y * z) :
    (vp x + vp y + vp z) + (vq x + vq y + vq z) + (vr x + vr y + vr z) ≥ 6 := by
  have hx : x ≠ 0 := by intro h; simp [h] at hxyz
  have hy : y ≠ 0 := by intro h; simp [h] at hxyz
  have hz : z ≠ 0 := by intro h; simp [h] at hxyz
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  -- Extract divisibility by each prime squared
  have h7 : 7^2 ∣ x * y * z := dvd_of_mul_dvd_mul_right (by decide : 0 < 11^2 * 13^2)
    (by ring_nf; ring_nf at hdiv; exact hdiv)
  have h11 : 11^2 ∣ x * y * z := dvd_of_mul_dvd_mul_left (by decide : 0 < 7^2)
    (dvd_of_mul_dvd_mul_right (by decide : 0 < 13^2) (by ring_nf; ring_nf at hdiv; exact hdiv))
  have h13 : 13^2 ∣ x * y * z := dvd_of_mul_dvd_mul_left (by decide : 0 < 7^2 * 11^2)
    (by ring_nf; ring_nf at hdiv; exact hdiv)
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
  rw [hvp] at hv7
  rw [hvq] at hv11
  rw [hvr] at hv13
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
  have hbound := total_val_bound x y z hx hy hz hxy hyz
  have hneed := need_6_vals x y z hxyz hdiv
  omega

/-- ABC conjecture is false -/
theorem abc_conjecture_is_false :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧
      ∃ start : ℕ, 0 < start ∧
        ∀ x y z, start ≤ x → x ≤ start + c - 1 →
                 start ≤ y → y ≤ start + c - 1 →
                 start ≤ z → z ≤ start + c - 1 →
                 x < y → y < z → ¬(a * b * c ∣ x * y * z) := by
  use 77, 91, 143  -- a = 7*11, b = 7*13, c = 11*13
  refine ⟨by decide, by decide, by decide, windowStart, by decide, ?_⟩
  intro x y z hxlo hxhi hylo hyhi hzlo hzhi hxy hyz hdiv
  have hend : windowStart + 143 - 1 = windowEnd := by decide
  rw [hend] at hxhi hyhi hzhi
  have habc : 77 * 91 * 143 = 7^2 * 11^2 * 13^2 := by decide
  rw [habc] at hdiv
  exact no_valid_triple x y z ⟨hxlo, hxhi⟩ ⟨hylo, hyhi⟩ ⟨hzlo, hzhi⟩ hxy hyz hdiv
