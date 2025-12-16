/-
# AcerFur's Proof v7: Streamlined

Use native_decide for all window-specific facts, then structural reasoning.
-/

import Mathlib.NumberTheory.Padics.PadicVal.Basic

instance : Fact (Nat.Prime 7) := ⟨by decide⟩
instance : Fact (Nat.Prime 11) := ⟨by decide⟩
instance : Fact (Nat.Prime 13) := ⟨by decide⟩

abbrev vp (n : ℕ) := padicValNat 7 n
abbrev vq (n : ℕ) := padicValNat 11 n
abbrev vr (n : ℕ) := padicValNat 13 n

/-! ## Core Facts -/

-- The window [5935, 6077]
def inWindow (x : ℕ) : Prop := 5935 ≤ x ∧ x ≤ 6077

instance : DecidablePred inWindow := fun x => by unfold inWindow; infer_instance

/-- No multiple of 169 in window -/
theorem no_169_in_window : ∀ x, inWindow x → ¬(169 ∣ x) := by
  intro x ⟨hlo, hhi⟩ ⟨k, hk⟩
  omega

/-- vr ≤ 1 for all x in window -/
theorem vr_le_one (x : ℕ) (hw : inWindow x) : vr x ≤ 1 := by
  by_contra h
  push_neg at h
  have hne : x ≠ 0 := by simp [inWindow] at hw; omega
  have h169 : 169 ∣ x := padicValNat_dvd_iff_le hne |>.mpr h
  exact no_169_in_window x hw h169

/-- 6006 is the only number in window divisible by 13 and by 7 or 11 -/
theorem only_6006_is_special : ∀ x, inWindow x → 13 ∣ x → (7 ∣ x ∨ 11 ∣ x) → x = 6006 := by
  intro x ⟨hlo, hhi⟩ h13 h7or11
  rcases h7or11 with h7 | h11
  · -- 91 | x (7*13)
    obtain ⟨k13, hk13⟩ := h13
    obtain ⟨k7, hk7⟩ := h7
    -- 91 = 7*13, multiples: 5915, 6006, 6097
    omega
  · -- 143 | x (11*13)
    obtain ⟨k13, hk13⟩ := h13
    obtain ⟨k11, hk11⟩ := h11
    -- 143 = 11*13, multiples: 5863, 6006, 6149
    omega

/-- 6006 is the only multiple of 77 in the window -/
theorem only_6006_div_77 : ∀ x, inWindow x → 77 ∣ x → x = 6006 := by
  intro x ⟨hlo, hhi⟩ h77
  obtain ⟨k, hk⟩ := h77
  -- 77 multiples: 5929, 6006, 6083
  omega

/-- No multiple of 5929 = 77*77 in window -/
theorem no_5929_in_window : ∀ x, inWindow x → 5929 ∣ x → False := by
  intro x ⟨hlo, hhi⟩ h
  obtain ⟨k, hk⟩ := h
  -- 5929 * 1 = 5929 < 5935, 5929 * 2 = 11858 > 6077
  omega

/-! ## Main Theorem -/

theorem no_valid_triple (x y z : ℕ)
    (hx : inWindow x) (hy : inWindow y) (hz : inWindow z)
    (hxy : x < y) (hyz : y < z)
    (hdiv : 7^2 * 11^2 * 13^2 ∣ x * y * z) : False := by
  -- Basic facts
  have hxne : x ≠ 0 := by simp [inWindow] at hx; omega
  have hyne : y ≠ 0 := by simp [inWindow] at hy; omega
  have hzne : z ≠ 0 := by simp [inWindow] at hz; omega
  have hxyne : x * y ≠ 0 := mul_ne_zero hxne hyne
  have hxyz : x * y * z ≠ 0 := mul_ne_zero hxyne hzne

  -- Extract divisibility by each prime squared
  have h7sq : 7^2 ∣ x * y * z := by
    have hdvd : 7^2 ∣ 7^2 * 11^2 * 13^2 := ⟨11^2 * 13^2, by ring⟩
    exact Nat.dvd_trans hdvd hdiv
  have h11sq : 11^2 ∣ x * y * z := by
    have hdvd : 11^2 ∣ 7^2 * 11^2 * 13^2 := ⟨7^2 * 13^2, by ring⟩
    exact Nat.dvd_trans hdvd hdiv
  have h13sq : 13^2 ∣ x * y * z := by
    have hdvd : 13^2 ∣ 7^2 * 11^2 * 13^2 := ⟨7^2 * 11^2, by ring⟩
    exact Nat.dvd_trans hdvd hdiv

  -- Convert to valuation bounds
  have hvp : vp x + vp y + vp z ≥ 2 := by
    have h := padicValNat_dvd_iff_le hxyz |>.mp h7sq
    have heq : vp (x * y * z) = vp x + vp y + vp z := by
      simp only [vp]; rw [padicValNat.mul hxyne hzne, padicValNat.mul hxne hyne]
    rw [← heq]; exact h
  have hvq : vq x + vq y + vq z ≥ 2 := by
    have h := padicValNat_dvd_iff_le hxyz |>.mp h11sq
    have heq : vq (x * y * z) = vq x + vq y + vq z := by
      simp only [vq]; rw [padicValNat.mul hxyne hzne, padicValNat.mul hxne hyne]
    rw [← heq]; exact h
  have hvr : vr x + vr y + vr z ≥ 2 := by
    have h := padicValNat_dvd_iff_le hxyz |>.mp h13sq
    have heq : vr (x * y * z) = vr x + vr y + vr z := by
      simp only [vr]; rw [padicValNat.mul hxyne hzne, padicValNat.mul hxne hyne]
    rw [← heq]; exact h

  -- Each vr is ≤ 1
  have hvr_x := vr_le_one x hx
  have hvr_y := vr_le_one y hy
  have hvr_z := vr_le_one z hz

  -- So at least 2 of {x, y, z} have vr = 1 (i.e., 13 | them)
  have htwo_13 : (vr x = 1 ∧ vr y = 1) ∨ (vr x = 1 ∧ vr z = 1) ∨ (vr y = 1 ∧ vr z = 1) := by
    omega

  -- vr n = 1 iff 13 | n (for n ≠ 0 in window)
  have h13_iff_vr1 : ∀ n, n ≠ 0 → (13 ∣ n ↔ vr n ≥ 1) := fun n hn => by
    constructor
    · intro h; exact one_le_padicValNat_of_dvd hn h
    · intro h; exact dvd_of_one_le_padicValNat h

  -- Helper: if 7|n and 11|n then 77|n
  have h77_of_7_11 : ∀ n, 7 ∣ n → 11 ∣ n → 77 ∣ n := fun n h7 h11 => by
    have hcop : Nat.Coprime 7 11 := by decide
    exact hcop.mul_dvd_of_dvd_of_dvd h7 h11

  -- Helper: if vp n ≥ 1 then 7 | n
  have h7_of_vp : ∀ n, vp n ≥ 1 → 7 ∣ n := fun n h => dvd_of_one_le_padicValNat h
  have h11_of_vq : ∀ n, vq n ≥ 1 → 11 ∣ n := fun n h => dvd_of_one_le_padicValNat h
  have h13_of_vr : ∀ n, vr n ≥ 1 → 13 ∣ n := fun n h => dvd_of_one_le_padicValNat h

  -- Case analysis on which two have 13 | them
  rcases htwo_13 with ⟨hvrx1, hvry1⟩ | ⟨hvrx1, hvrz1⟩ | ⟨hvry1, hvrz1⟩

  · -- Case 1: 13 | x and 13 | y
    have h13x : 13 ∣ x := h13_of_vr x (by omega : vr x ≥ 1)
    have h13y : 13 ∣ y := h13_of_vr y (by omega : vr y ≥ 1)

    -- Subcase: is x = 6006?
    by_cases hx6 : x = 6006
    · -- x = 6006, so y > 6006 and 13 | y
      -- y is not 6006, so y is "pure 13" (not divisible by 7 or 11)
      have hy6 : y ≠ 6006 := by omega
      have hy_no7 : ¬(7 ∣ y) := fun h => hy6 (only_6006_is_special y hy h13y (Or.inl h))
      have hy_no11 : ¬(11 ∣ y) := fun h => hy6 (only_6006_is_special y hy h13y (Or.inr h))
      have hvpy : vp y = 0 := padicValNat.eq_zero_of_not_dvd hy_no7
      have hvqy : vq y = 0 := padicValNat.eq_zero_of_not_dvd hy_no11

      -- x = 6006 has vp = vq = 1
      have hvpx : vp x = 1 := by subst hx6; native_decide
      have hvqx : vq x = 1 := by subst hx6; native_decide

      -- So vp z ≥ 1 and vq z ≥ 1
      have hvpz : vp z ≥ 1 := by omega
      have hvqz : vq z ≥ 1 := by omega

      -- So 7 | z and 11 | z, hence 77 | z
      have h7z : 7 ∣ z := h7_of_vp z hvpz
      have h11z : 11 ∣ z := h11_of_vq z hvqz
      have h77z : 77 ∣ z := h77_of_7_11 z h7z h11z

      -- Only 6006 is divisible by 77 in window
      have hz6 : z = 6006 := only_6006_div_77 z hz h77z
      -- But x = 6006 and x < y < z, contradiction
      omega

    · -- x ≠ 6006 and 13 | x, so x is pure 13
      have hx_no7 : ¬(7 ∣ x) := fun h => hx6 (only_6006_is_special x hx h13x (Or.inl h))
      have hx_no11 : ¬(11 ∣ x) := fun h => hx6 (only_6006_is_special x hx h13x (Or.inr h))
      have hvpx : vp x = 0 := padicValNat.eq_zero_of_not_dvd hx_no7
      have hvqx : vq x = 0 := padicValNat.eq_zero_of_not_dvd hx_no11

      by_cases hy6 : y = 6006
      · -- y = 6006
        have hvpy : vp y = 1 := by subst hy6; native_decide
        have hvqy : vq y = 1 := by subst hy6; native_decide
        have hvpz : vp z ≥ 1 := by omega
        have hvqz : vq z ≥ 1 := by omega
        have h7z : 7 ∣ z := h7_of_vp z hvpz
        have h11z : 11 ∣ z := h11_of_vq z hvqz
        have h77z : 77 ∣ z := h77_of_7_11 z h7z h11z
        have hz6 : z = 6006 := only_6006_div_77 z hz h77z
        omega

      · -- Neither x nor y is 6006
        have hy_no7 : ¬(7 ∣ y) := fun h => hy6 (only_6006_is_special y hy h13y (Or.inl h))
        have hy_no11 : ¬(11 ∣ y) := fun h => hy6 (only_6006_is_special y hy h13y (Or.inr h))
        have hvpy : vp y = 0 := padicValNat.eq_zero_of_not_dvd hy_no7
        have hvqy : vq y = 0 := padicValNat.eq_zero_of_not_dvd hy_no11

        -- vp z ≥ 2 and vq z ≥ 2 needed
        have hvpz : vp z ≥ 2 := by omega
        have hvqz : vq z ≥ 2 := by omega

        -- 49 | z and 121 | z
        have h49z : 49 ∣ z := padicValNat_dvd_iff_le hzne |>.mpr hvpz
        have h121z : 121 ∣ z := padicValNat_dvd_iff_le hzne |>.mpr hvqz

        -- 49 and 121 are coprime, so 5929 | z
        have hcop : Nat.Coprime 49 121 := by decide
        have h5929z : 5929 ∣ z := hcop.mul_dvd_of_dvd_of_dvd h49z h121z

        -- But no multiple of 5929 in window
        exact no_5929_in_window z hz h5929z

  · -- Case 2: 13 | x and 13 | z (symmetric to case 1 with y↔z swapped in some places)
    have h13x : 13 ∣ x := h13_of_vr x (by omega)
    have h13z : 13 ∣ z := h13_of_vr z (by omega)

    by_cases hx6 : x = 6006
    · have hz6 : z ≠ 6006 := by omega
      have hz_no7 : ¬(7 ∣ z) := fun h => hz6 (only_6006_is_special z hz h13z (Or.inl h))
      have hz_no11 : ¬(11 ∣ z) := fun h => hz6 (only_6006_is_special z hz h13z (Or.inr h))
      have hvpz : vp z = 0 := padicValNat.eq_zero_of_not_dvd hz_no7
      have hvqz : vq z = 0 := padicValNat.eq_zero_of_not_dvd hz_no11
      have hvpx : vp x = 1 := by subst hx6; native_decide
      have hvqx : vq x = 1 := by subst hx6; native_decide
      have hvpy : vp y ≥ 1 := by omega
      have hvqy : vq y ≥ 1 := by omega
      have h7y : 7 ∣ y := h7_of_vp y hvpy
      have h11y : 11 ∣ y := h11_of_vq y hvqy
      have h77y : 77 ∣ y := h77_of_7_11 y h7y h11y
      have hy6 : y = 6006 := only_6006_div_77 y hy h77y
      omega
    · have hx_no7 : ¬(7 ∣ x) := fun h => hx6 (only_6006_is_special x hx h13x (Or.inl h))
      have hx_no11 : ¬(11 ∣ x) := fun h => hx6 (only_6006_is_special x hx h13x (Or.inr h))
      have hvpx : vp x = 0 := padicValNat.eq_zero_of_not_dvd hx_no7
      have hvqx : vq x = 0 := padicValNat.eq_zero_of_not_dvd hx_no11

      by_cases hz6 : z = 6006
      · have hvpz : vp z = 1 := by subst hz6; native_decide
        have hvqz : vq z = 1 := by subst hz6; native_decide
        have hvpy : vp y ≥ 1 := by omega
        have hvqy : vq y ≥ 1 := by omega
        have h7y : 7 ∣ y := h7_of_vp y hvpy
        have h11y : 11 ∣ y := h11_of_vq y hvqy
        have h77y : 77 ∣ y := h77_of_7_11 y h7y h11y
        have hy6 : y = 6006 := only_6006_div_77 y hy h77y
        omega
      · have hz_no7 : ¬(7 ∣ z) := fun h => hz6 (only_6006_is_special z hz h13z (Or.inl h))
        have hz_no11 : ¬(11 ∣ z) := fun h => hz6 (only_6006_is_special z hz h13z (Or.inr h))
        have hvpz : vp z = 0 := padicValNat.eq_zero_of_not_dvd hz_no7
        have hvqz : vq z = 0 := padicValNat.eq_zero_of_not_dvd hz_no11
        have hvpy : vp y ≥ 2 := by omega
        have hvqy : vq y ≥ 2 := by omega
        have h49y : 49 ∣ y := padicValNat_dvd_iff_le hyne |>.mpr hvpy
        have h121y : 121 ∣ y := padicValNat_dvd_iff_le hyne |>.mpr hvqy
        have hcop : Nat.Coprime 49 121 := by decide
        have h5929y : 5929 ∣ y := hcop.mul_dvd_of_dvd_of_dvd h49y h121y
        exact no_5929_in_window y hy h5929y

  · -- Case 3: 13 | y and 13 | z
    have h13y : 13 ∣ y := h13_of_vr y (by omega)
    have h13z : 13 ∣ z := h13_of_vr z (by omega)

    by_cases hy6 : y = 6006
    · have hz6 : z ≠ 6006 := by omega
      have hz_no7 : ¬(7 ∣ z) := fun h => hz6 (only_6006_is_special z hz h13z (Or.inl h))
      have hz_no11 : ¬(11 ∣ z) := fun h => hz6 (only_6006_is_special z hz h13z (Or.inr h))
      have hvpz : vp z = 0 := padicValNat.eq_zero_of_not_dvd hz_no7
      have hvqz : vq z = 0 := padicValNat.eq_zero_of_not_dvd hz_no11
      have hvpy : vp y = 1 := by subst hy6; native_decide
      have hvqy : vq y = 1 := by subst hy6; native_decide
      have hvpx : vp x ≥ 1 := by omega
      have hvqx : vq x ≥ 1 := by omega
      have h7x : 7 ∣ x := h7_of_vp x hvpx
      have h11x : 11 ∣ x := h11_of_vq x hvqx
      have h77x : 77 ∣ x := h77_of_7_11 x h7x h11x
      have hx6 : x = 6006 := only_6006_div_77 x hx h77x
      omega
    · have hy_no7 : ¬(7 ∣ y) := fun h => hy6 (only_6006_is_special y hy h13y (Or.inl h))
      have hy_no11 : ¬(11 ∣ y) := fun h => hy6 (only_6006_is_special y hy h13y (Or.inr h))
      have hvpy : vp y = 0 := padicValNat.eq_zero_of_not_dvd hy_no7
      have hvqy : vq y = 0 := padicValNat.eq_zero_of_not_dvd hy_no11

      by_cases hz6 : z = 6006
      · have hvpz : vp z = 1 := by subst hz6; native_decide
        have hvqz : vq z = 1 := by subst hz6; native_decide
        have hvpx : vp x ≥ 1 := by omega
        have hvqx : vq x ≥ 1 := by omega
        have h7x : 7 ∣ x := h7_of_vp x hvpx
        have h11x : 11 ∣ x := h11_of_vq x hvqx
        have h77x : 77 ∣ x := h77_of_7_11 x h7x h11x
        have hx6 : x = 6006 := only_6006_div_77 x hx h77x
        omega
      · have hz_no7 : ¬(7 ∣ z) := fun h => hz6 (only_6006_is_special z hz h13z (Or.inl h))
        have hz_no11 : ¬(11 ∣ z) := fun h => hz6 (only_6006_is_special z hz h13z (Or.inr h))
        have hvpz : vp z = 0 := padicValNat.eq_zero_of_not_dvd hz_no7
        have hvqz : vq z = 0 := padicValNat.eq_zero_of_not_dvd hz_no11
        have hvpx : vp x ≥ 2 := by omega
        have hvqx : vq x ≥ 2 := by omega
        have h49x : 49 ∣ x := padicValNat_dvd_iff_le hxne |>.mpr hvpx
        have h121x : 121 ∣ x := padicValNat_dvd_iff_le hxne |>.mpr hvqx
        have hcop : Nat.Coprime 49 121 := by decide
        have h5929x : 5929 ∣ x := hcop.mul_dvd_of_dvd_of_dvd h49x h121x
        exact no_5929_in_window x hx h5929x

/-- ABC conjecture is false -/
theorem abc_conjecture_is_false :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧
      ∃ start : ℕ, 0 < start ∧
        ∀ x y z, start ≤ x → x ≤ start + c - 1 →
                 start ≤ y → y ≤ start + c - 1 →
                 start ≤ z → z ≤ start + c - 1 →
                 x < y → y < z → ¬(a * b * c ∣ x * y * z) := by
  use 77, 91, 143
  refine ⟨by decide, by decide, by decide, 5935, by decide, ?_⟩
  intro x y z hxlo hxhi hylo hyhi hzlo hzhi hxy hyz hdiv
  have hend : 5935 + 143 - 1 = 6077 := by decide
  rw [hend] at hxhi hyhi hzhi
  have habc : 77 * 91 * 143 = 7^2 * 11^2 * 13^2 := by decide
  rw [habc] at hdiv
  exact no_valid_triple x y z ⟨hxlo, hxhi⟩ ⟨hylo, hyhi⟩ ⟨hzlo, hzhi⟩ hxy hyz hdiv
