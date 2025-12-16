/-
# AcerFur's Proof v6: Correct Logic

Key insight: we need vr(xyz) ≥ 2, but no 13² in window, so TWO of x,y,z must be ∣ 13.
But 6006 is the only multiple of 13 that also divides 7 or 11.
This leads to a contradiction.
-/

import Mathlib.NumberTheory.Padics.PadicVal.Basic

instance hp7 : Fact (Nat.Prime 7) := ⟨by decide⟩
instance hp11 : Fact (Nat.Prime 11) := ⟨by decide⟩
instance hp13 : Fact (Nat.Prime 13) := ⟨by decide⟩

def windowStart : ℕ := 5935
def windowEnd : ℕ := 6077

abbrev vp (n : ℕ) := padicValNat 7 n
abbrev vq (n : ℕ) := padicValNat 11 n
abbrev vr (n : ℕ) := padicValNat 13 n

/-! ## Core Facts (Computational) -/

/-- 6006 is the only number in window divisible by 13 and (7 or 11) -/
def check6006Only : Bool :=
  (List.range (windowEnd - windowStart + 1)).all fun i =>
    let x := windowStart + i
    ¬(13 ∣ x ∧ (7 ∣ x ∨ 11 ∣ x)) ∨ x = 6006

theorem check_6006_only : check6006Only = true := by native_decide

/-- No multiple of 169 in window -/
def checkNo169 : Bool :=
  (List.range (windowEnd - windowStart + 1)).all fun i =>
    let x := windowStart + i
    ¬(169 ∣ x)

theorem check_no_169 : checkNo169 = true := by native_decide

/-- vr x ≤ 1 for all x in window -/
theorem vr_le_one (x : ℕ) (hlo : windowStart ≤ x) (hhi : x ≤ windowEnd) : vr x ≤ 1 := by
  by_contra h
  push_neg at h
  have h2 : 13^2 ∣ x := padicValNat_dvd_iff_le (by omega : x ≠ 0) |>.mpr h
  have hcheck := check_no_169
  simp only [checkNo169, List.all_eq_true, List.mem_range, decide_eq_true_eq,
             windowStart, windowEnd] at hcheck
  have hi : x - 5935 < 6077 - 5935 + 1 := by omega
  specialize hcheck (x - 5935) hi
  simp only [Nat.add_sub_cancel'] at hcheck
  have heq : 5935 + (x - 5935) = x := by omega
  rw [heq] at hcheck
  exact hcheck h2

/-- 6006 is the only number in window divisible by 13 AND (7 or 11) -/
theorem only_6006_multi_13 (x : ℕ) (hlo : windowStart ≤ x) (hhi : x ≤ windowEnd)
    (h13 : 13 ∣ x) (h7or11 : 7 ∣ x ∨ 11 ∣ x) : x = 6006 := by
  have hcheck := check_6006_only
  simp only [check6006Only, List.all_eq_true, List.mem_range, decide_eq_true_eq,
             not_and, windowStart, windowEnd] at hcheck
  have hi : x - 5935 < 6077 - 5935 + 1 := by omega
  specialize hcheck (x - 5935) hi
  have heq : 5935 + (x - 5935) = x := by omega
  simp only [heq] at hcheck
  cases hcheck (And.intro h13 h7or11) with
  | inl h => exact absurd h13 h
  | inr h => exact h

/-! ## The Main Argument -/

theorem no_valid_triple (x y z : ℕ)
    (hx : windowStart ≤ x ∧ x ≤ windowEnd)
    (hy : windowStart ≤ y ∧ y ≤ windowEnd)
    (hz : windowStart ≤ z ∧ z ≤ windowEnd)
    (hxy : x < y) (hyz : y < z)
    (hdiv : 7^2 * 11^2 * 13^2 ∣ x * y * z) : False := by
  have hxyz : x * y * z ≠ 0 := by simp only [windowStart] at hx hy hz; omega
  have hxne : x ≠ 0 := by omega
  have hyne : y ≠ 0 := by omega
  have hzne : z ≠ 0 := by omega
  have hxyne : x * y ≠ 0 := mul_ne_zero hxne hyne

  -- Extract: 13² | xyz
  have h13 : 13^2 ∣ x * y * z := by
    have : 7^2 * 11^2 * 13^2 = 13^2 * (7^2 * 11^2) := by ring
    rw [this] at hdiv
    exact Nat.dvd_of_mul_dvd_mul_right (by decide : 0 < 7^2 * 11^2) hdiv

  -- Since vr ≤ 1 for each, we need vr x + vr y + vr z ≥ 2
  -- So at least TWO of x, y, z have vr = 1 (i.e., 13 ∣ them)
  have hvr_xyz : vr (x * y * z) ≥ 2 := padicValNat_dvd_iff_le hxyz |>.mp h13
  have hvr_sum : vr (x * y * z) = vr x + vr y + vr z := by
    simp only [vr]
    rw [padicValNat.mul hxyne hzne, padicValNat.mul hxne hyne]
  rw [hvr_sum] at hvr_xyz

  have hvr_x := vr_le_one x hx.1 hx.2
  have hvr_y := vr_le_one y hy.1 hy.2
  have hvr_z := vr_le_one z hz.1 hz.2

  -- At least two of vr x, vr y, vr z must be ≥ 1
  -- Case analysis: which two?
  have htwo : (vr x ≥ 1 ∧ vr y ≥ 1) ∨ (vr x ≥ 1 ∧ vr z ≥ 1) ∨ (vr y ≥ 1 ∧ vr z ≥ 1) := by
    omega

  -- vr n ≥ 1 iff 13 ∣ n
  have h13_x : vr x ≥ 1 ↔ 13 ∣ x := by
    constructor
    · intro h; exact dvd_of_one_le_padicValNat h
    · intro h; exact one_le_padicValNat_of_dvd hxne h
  have h13_y : vr y ≥ 1 ↔ 13 ∣ y := by
    constructor
    · intro h; exact dvd_of_one_le_padicValNat h
    · intro h; exact one_le_padicValNat_of_dvd hyne h
  have h13_z : vr z ≥ 1 ↔ 13 ∣ z := by
    constructor
    · intro h; exact dvd_of_one_le_padicValNat h
    · intro h; exact one_le_padicValNat_of_dvd hzne h

  -- Similarly extract 7² | xyz and 11² | xyz
  have h7 : 7^2 ∣ x * y * z := by
    have : 7^2 * 11^2 * 13^2 = 7^2 * (11^2 * 13^2) := by ring
    rw [this] at hdiv
    exact Nat.dvd_of_mul_dvd_mul_right (by decide : 0 < 11^2 * 13^2) hdiv
  have h11 : 11^2 ∣ x * y * z := by
    have : 7^2 * 11^2 * 13^2 = 11^2 * (7^2 * 13^2) := by ring
    rw [this] at hdiv
    exact Nat.dvd_of_mul_dvd_mul_right (by decide : 0 < 7^2 * 13^2) hdiv

  have hvp_xyz : vp (x * y * z) ≥ 2 := padicValNat_dvd_iff_le hxyz |>.mp h7
  have hvq_xyz : vq (x * y * z) ≥ 2 := padicValNat_dvd_iff_le hxyz |>.mp h11

  have hvp_sum : vp (x * y * z) = vp x + vp y + vp z := by
    simp only [vp]; rw [padicValNat.mul hxyne hzne, padicValNat.mul hxne hyne]
  have hvq_sum : vq (x * y * z) = vq x + vq y + vq z := by
    simp only [vq]; rw [padicValNat.mul hxyne hzne, padicValNat.mul hxne hyne]

  rw [hvp_sum] at hvp_xyz
  rw [hvq_sum] at hvq_xyz

  -- Now case analysis on which two have 13 | them
  rcases htwo with ⟨hvrx, hvry⟩ | ⟨hvrx, hvrz⟩ | ⟨hvry, hvrz⟩

  · -- Case: 13 | x and 13 | y, but not necessarily 13 | z
    have h13x : 13 ∣ x := h13_x.mp hvrx
    have h13y : 13 ∣ y := h13_y.mp hvry
    -- z contributes vr z ≤ 1, and vr x = vr y = 1
    -- So vp and vq must come from x, y, z
    -- Since vr x = vr y = 1 and 13 | x, 13 | y
    -- If x also has 7|x or 11|x, then x = 6006
    -- Similarly for y

    -- We need vp(xyz) ≥ 2 and vq(xyz) ≥ 2
    -- Total of 4 needed from vp and vq

    -- Subcase: x = 6006
    by_cases hx6 : x = 6006
    · -- Then y > 6006, and 13 | y
      -- y ≠ 6006, so y is "pure 13" (not divisible by 7 or 11)
      have hy6 : y ≠ 6006 := by omega
      have hy_no7 : ¬(7 ∣ y) := by
        intro h7y
        have := only_6006_multi_13 y hy.1 hy.2 h13y (Or.inl h7y)
        exact hy6 this
      have hy_no11 : ¬(11 ∣ y) := by
        intro h11y
        have := only_6006_multi_13 y hy.1 hy.2 h13y (Or.inr h11y)
        exact hy6 this
      have hvpy : vp y = 0 := padicValNat.eq_zero_of_not_dvd hy_no7
      have hvqy : vq y = 0 := padicValNat.eq_zero_of_not_dvd hy_no11

      -- x = 6006 gives vp = 1, vq = 1
      have hvpx : vp x = 1 := by simp [hx6, vp]; native_decide
      have hvqx : vq x = 1 := by simp [hx6, vq]; native_decide

      -- So vp z + vq z ≥ 2 (need 1 more for each)
      have hvpz : vp z ≥ 1 := by omega
      have hvqz : vq z ≥ 1 := by omega

      have h7z : 7 ∣ z := dvd_of_one_le_padicValNat hvpz
      have h11z : 11 ∣ z := dvd_of_one_le_padicValNat hvqz

      -- z is divisible by both 7 and 11, so z = 6006
      -- But then 13 | z too, and z = 6006 contradicts y < z with y > 6006
      have hz6 : z = 6006 := by
        have h13z_or : 13 ∣ z ∨ ¬(13 ∣ z) := em _
        cases h13z_or with
        | inl h13z =>
          exact only_6006_multi_13 z hz.1 hz.2 h13z (Or.inl h7z)
        | inr h13z =>
          -- z not divisible by 13, but 7|z and 11|z
          -- 6006 = 7*11*13*6, next 7*11 multiple is 6083 > 6077
          -- So z = 6006? No, 6006 is divisible by 13...
          -- Actually if 7|z and 11|z and ¬13|z, then 77|z
          -- Multiples of 77 in window: 5929, 6006, 6083
          -- 5929 < 5935, 6083 > 6077, 6006 is divisible by 13
          -- Contradiction!
          have h77z : 77 ∣ z := Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 1) (by
            have : 7 * 11 = 77 := by ring
            rw [← this]
            exact Nat.mul_dvd_mul h7z h11z)
          -- Check: only 77 multiple in window is 6006
          have : z = 6006 := by
            simp only [windowStart, windowEnd] at hz
            omega
          exact absurd (by simp [this] : 13 ∣ z) h13z
      omega  -- z = 6006 but y < z and y > 6006

    · -- x ≠ 6006, 13 | x
      have hx_no7 : ¬(7 ∣ x) := by
        intro h7x
        have := only_6006_multi_13 x hx.1 hx.2 h13x (Or.inl h7x)
        exact hx6 this
      have hx_no11 : ¬(11 ∣ x) := by
        intro h11x
        have := only_6006_multi_13 x hx.1 hx.2 h13x (Or.inr h11x)
        exact hx6 this
      have hvpx : vp x = 0 := padicValNat.eq_zero_of_not_dvd hx_no7
      have hvqx : vq x = 0 := padicValNat.eq_zero_of_not_dvd hx_no11

      -- Similarly for y
      by_cases hy6 : y = 6006
      · -- y = 6006, x < y = 6006, 13|x, x is pure 13
        have hvpy : vp y = 1 := by simp [hy6, vp]; native_decide
        have hvqy : vq y = 1 := by simp [hy6, vq]; native_decide
        -- Need vp z ≥ 1 and vq z ≥ 1
        have hvpz : vp z ≥ 1 := by omega
        have hvqz : vq z ≥ 1 := by omega
        have h7z : 7 ∣ z := dvd_of_one_le_padicValNat hvpz
        have h11z : 11 ∣ z := dvd_of_one_le_padicValNat hvqz
        -- Same argument: 77|z, only option is 6006, but y < z
        have h77z : 77 ∣ z := Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 1) (by
          have : 7 * 11 = 77 := by ring; rw [← this]; exact Nat.mul_dvd_mul h7z h11z)
        have hz6 : z = 6006 := by simp only [windowStart, windowEnd] at hz; omega
        omega

      · -- Neither x nor y is 6006, both are pure 13
        have hy_no7 : ¬(7 ∣ y) := by
          intro h7y; have := only_6006_multi_13 y hy.1 hy.2 h13y (Or.inl h7y); exact hy6 this
        have hy_no11 : ¬(11 ∣ y) := by
          intro h11y; have := only_6006_multi_13 y hy.1 hy.2 h13y (Or.inr h11y); exact hy6 this
        have hvpy : vp y = 0 := padicValNat.eq_zero_of_not_dvd hy_no7
        have hvqy : vq y = 0 := padicValNat.eq_zero_of_not_dvd hy_no11
        -- vp z ≥ 2 and vq z ≥ 2 needed
        have hvpz : vp z ≥ 2 := by omega
        have hvqz : vq z ≥ 2 := by omega
        -- So 49 | z and 121 | z, meaning 49*121 = 5929 | z
        -- But 5929 > windowEnd... wait no
        have h49z : 49 ∣ z := padicValNat_dvd_iff_le hzne |>.mpr hvpz
        have h121z : 121 ∣ z := padicValNat_dvd_iff_le hzne |>.mpr hvqz
        -- 49 and 121 are coprime (7² and 11²)
        have hcop : Nat.Coprime 49 121 := by decide
        have h5929z : 5929 ∣ z := by
          have := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h49z h121z
          convert this using 1; ring
        -- But z ∈ [5935, 6077], and 5929 | z means z ∈ {5929, 11858, ...}
        -- 5929 < 5935, 11858 > 6077. Contradiction!
        simp only [windowStart, windowEnd] at hz
        omega

  · -- Case: 13 | x and 13 | z (symmetric, just swap y↔z in logic)
    have h13x : 13 ∣ x := h13_x.mp hvrx
    have h13z : 13 ∣ z := h13_z.mp hvrz

    by_cases hx6 : x = 6006
    · have hz6 : z ≠ 6006 := by omega
      have hz_no7 : ¬(7 ∣ z) := by
        intro h7z; have := only_6006_multi_13 z hz.1 hz.2 h13z (Or.inl h7z); exact hz6 this
      have hz_no11 : ¬(11 ∣ z) := by
        intro h11z; have := only_6006_multi_13 z hz.1 hz.2 h13z (Or.inr h11z); exact hz6 this
      have hvpz : vp z = 0 := padicValNat.eq_zero_of_not_dvd hz_no7
      have hvqz : vq z = 0 := padicValNat.eq_zero_of_not_dvd hz_no11
      have hvpx : vp x = 1 := by simp [hx6, vp]; native_decide
      have hvqx : vq x = 1 := by simp [hx6, vq]; native_decide
      have hvpy : vp y ≥ 1 := by omega
      have hvqy : vq y ≥ 1 := by omega
      have h7y : 7 ∣ y := dvd_of_one_le_padicValNat hvpy
      have h11y : 11 ∣ y := dvd_of_one_le_padicValNat hvqy
      have h77y : 77 ∣ y := Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 1) (by
        have : 7 * 11 = 77 := by ring; rw [← this]; exact Nat.mul_dvd_mul h7y h11y)
      have hy6 : y = 6006 := by simp only [windowStart, windowEnd] at hy; omega
      omega
    · have hx_no7 : ¬(7 ∣ x) := by
        intro h7x; have := only_6006_multi_13 x hx.1 hx.2 h13x (Or.inl h7x); exact hx6 this
      have hx_no11 : ¬(11 ∣ x) := by
        intro h11x; have := only_6006_multi_13 x hx.1 hx.2 h13x (Or.inr h11x); exact hx6 this
      have hvpx : vp x = 0 := padicValNat.eq_zero_of_not_dvd hx_no7
      have hvqx : vq x = 0 := padicValNat.eq_zero_of_not_dvd hx_no11

      by_cases hz6 : z = 6006
      · have hvpz : vp z = 1 := by simp [hz6, vp]; native_decide
        have hvqz : vq z = 1 := by simp [hz6, vq]; native_decide
        have hvpy : vp y ≥ 1 := by omega
        have hvqy : vq y ≥ 1 := by omega
        have h7y : 7 ∣ y := dvd_of_one_le_padicValNat hvpy
        have h11y : 11 ∣ y := dvd_of_one_le_padicValNat hvqy
        have h77y : 77 ∣ y := Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 1) (by
          have : 7 * 11 = 77 := by ring; rw [← this]; exact Nat.mul_dvd_mul h7y h11y)
        have hy6 : y = 6006 := by simp only [windowStart, windowEnd] at hy; omega
        omega
      · have hz_no7 : ¬(7 ∣ z) := by
          intro h7z; have := only_6006_multi_13 z hz.1 hz.2 h13z (Or.inl h7z); exact hz6 this
        have hz_no11 : ¬(11 ∣ z) := by
          intro h11z; have := only_6006_multi_13 z hz.1 hz.2 h13z (Or.inr h11z); exact hz6 this
        have hvpz : vp z = 0 := padicValNat.eq_zero_of_not_dvd hz_no7
        have hvqz : vq z = 0 := padicValNat.eq_zero_of_not_dvd hz_no11
        have hvpy : vp y ≥ 2 := by omega
        have hvqy : vq y ≥ 2 := by omega
        have h49y : 49 ∣ y := padicValNat_dvd_iff_le hyne |>.mpr hvpy
        have h121y : 121 ∣ y := padicValNat_dvd_iff_le hyne |>.mpr hvqy
        have hcop : Nat.Coprime 49 121 := by decide
        have h5929y : 5929 ∣ y := by
          have := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h49y h121y
          convert this using 1; ring
        simp only [windowStart, windowEnd] at hy
        omega

  · -- Case: 13 | y and 13 | z
    have h13y : 13 ∣ y := h13_y.mp hvry
    have h13z : 13 ∣ z := h13_z.mp hvrz
    -- x doesn't need to be divisible by 13
    -- vp and vq must come from x, y, z combined

    by_cases hy6 : y = 6006
    · have hz6 : z ≠ 6006 := by omega
      have hz_no7 : ¬(7 ∣ z) := by
        intro h7z; have := only_6006_multi_13 z hz.1 hz.2 h13z (Or.inl h7z); exact hz6 this
      have hz_no11 : ¬(11 ∣ z) := by
        intro h11z; have := only_6006_multi_13 z hz.1 hz.2 h13z (Or.inr h11z); exact hz6 this
      have hvpz : vp z = 0 := padicValNat.eq_zero_of_not_dvd hz_no7
      have hvqz : vq z = 0 := padicValNat.eq_zero_of_not_dvd hz_no11
      have hvpy : vp y = 1 := by simp [hy6, vp]; native_decide
      have hvqy : vq y = 1 := by simp [hy6, vq]; native_decide
      have hvpx : vp x ≥ 1 := by omega
      have hvqx : vq x ≥ 1 := by omega
      have h7x : 7 ∣ x := dvd_of_one_le_padicValNat hvpx
      have h11x : 11 ∣ x := dvd_of_one_le_padicValNat hvqx
      have h77x : 77 ∣ x := Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 1) (by
        have : 7 * 11 = 77 := by ring; rw [← this]; exact Nat.mul_dvd_mul h7x h11x)
      have hx6 : x = 6006 := by simp only [windowStart, windowEnd] at hx; omega
      omega
    · have hy_no7 : ¬(7 ∣ y) := by
        intro h7y; have := only_6006_multi_13 y hy.1 hy.2 h13y (Or.inl h7y); exact hy6 this
      have hy_no11 : ¬(11 ∣ y) := by
        intro h11y; have := only_6006_multi_13 y hy.1 hy.2 h13y (Or.inr h11y); exact hy6 this
      have hvpy : vp y = 0 := padicValNat.eq_zero_of_not_dvd hy_no7
      have hvqy : vq y = 0 := padicValNat.eq_zero_of_not_dvd hy_no11

      by_cases hz6 : z = 6006
      · have hvpz : vp z = 1 := by simp [hz6, vp]; native_decide
        have hvqz : vq z = 1 := by simp [hz6, vq]; native_decide
        have hvpx : vp x ≥ 1 := by omega
        have hvqx : vq x ≥ 1 := by omega
        have h7x : 7 ∣ x := dvd_of_one_le_padicValNat hvpx
        have h11x : 11 ∣ x := dvd_of_one_le_padicValNat hvqx
        have h77x : 77 ∣ x := Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 1) (by
          have : 7 * 11 = 77 := by ring; rw [← this]; exact Nat.mul_dvd_mul h7x h11x)
        have hx6 : x = 6006 := by simp only [windowStart, windowEnd] at hx; omega
        omega
      · have hz_no7 : ¬(7 ∣ z) := by
          intro h7z; have := only_6006_multi_13 z hz.1 hz.2 h13z (Or.inl h7z); exact hz6 this
        have hz_no11 : ¬(11 ∣ z) := by
          intro h11z; have := only_6006_multi_13 z hz.1 hz.2 h13z (Or.inr h11z); exact hz6 this
        have hvpz : vp z = 0 := padicValNat.eq_zero_of_not_dvd hz_no7
        have hvqz : vq z = 0 := padicValNat.eq_zero_of_not_dvd hz_no11
        have hvpx : vp x ≥ 2 := by omega
        have hvqx : vq x ≥ 2 := by omega
        have h49x : 49 ∣ x := padicValNat_dvd_iff_le hxne |>.mpr hvpx
        have h121x : 121 ∣ x := padicValNat_dvd_iff_le hxne |>.mpr hvqx
        have hcop : Nat.Coprime 49 121 := by decide
        have h5929x : 5929 ∣ x := by
          have := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h49x h121x
          convert this using 1; ring
        simp only [windowStart, windowEnd] at hx
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
