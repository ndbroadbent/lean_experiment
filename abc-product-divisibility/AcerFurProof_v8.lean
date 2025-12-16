/-
# AcerFur's Proof v8: Refactored for Elegance

Key improvements over v7:
1. Helper lemmas for padicValNat multiplication (handles zero cases)
2. Abstracted "exists_pure13" to eliminate case repetition
3. Cleaner structural flow
-/

import Mathlib.NumberTheory.Padics.PadicVal.Basic

instance : Fact (Nat.Prime 7) := ⟨by decide⟩
instance : Fact (Nat.Prime 11) := ⟨by decide⟩
instance : Fact (Nat.Prime 13) := ⟨by decide⟩

abbrev vp (n : ℕ) := padicValNat 7 n
abbrev vq (n : ℕ) := padicValNat 11 n
abbrev vr (n : ℕ) := padicValNat 13 n

/-! ## Helper Lemmas for padicValNat -/

/-- Triple product valuation with explicit non-zero proofs -/
lemma padicValNat_mul3 (p x y z : ℕ) [Fact (Nat.Prime p)] (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    padicValNat p (x * y * z) = padicValNat p x + padicValNat p y + padicValNat p z := by
  rw [padicValNat.mul (mul_ne_zero hx hy) hz, padicValNat.mul hx hy]

/-- If sum of three values each ≤ 1 is ≥ 2, then two of them equal 1 -/
lemma two_eq_one_of_sum_ge_two {a b c : ℕ} (ha : a ≤ 1) (hb : b ≤ 1) (hc : c ≤ 1)
    (hsum : a + b + c ≥ 2) : (a = 1 ∧ b = 1) ∨ (a = 1 ∧ c = 1) ∨ (b = 1 ∧ c = 1) := by
  omega

/-! ## Window Facts -/

def inWindow (x : ℕ) : Prop := 5935 ≤ x ∧ x ≤ 6077

theorem no_169_in_window : ∀ x, inWindow x → ¬(169 ∣ x) := by
  intro x ⟨hlo, hhi⟩ ⟨k, hk⟩; omega

theorem vr_le_one (x : ℕ) (hw : inWindow x) : vr x ≤ 1 := by
  by_contra h; push_neg at h
  have hne : x ≠ 0 := by simp [inWindow] at hw; omega
  have h169 : 169 ∣ x := padicValNat_dvd_iff_le hne |>.mpr h
  exact no_169_in_window x hw h169

theorem only_6006_is_special : ∀ x, inWindow x → 13 ∣ x → (7 ∣ x ∨ 11 ∣ x) → x = 6006 := by
  intro x ⟨hlo, hhi⟩ h13 h7or11
  rcases h7or11 with h7 | h11
  · obtain ⟨_, _⟩ := h13; obtain ⟨_, _⟩ := h7; omega
  · obtain ⟨_, _⟩ := h13; obtain ⟨_, _⟩ := h11; omega

theorem only_6006_div_77 : ∀ x, inWindow x → 77 ∣ x → x = 6006 := by
  intro x ⟨hlo, hhi⟩ ⟨k, hk⟩; omega

theorem no_5929_in_window : ∀ x, inWindow x → 5929 ∣ x → False := by
  intro x ⟨hlo, hhi⟩ ⟨k, hk⟩; omega

/-! ## The Key Structural Lemma -/

/-- Among any two 13-multiples in the window, at least one is "pure 13" (not divisible by 7 or 11) -/
lemma exists_pure13_of_two_div_13 {a b : ℕ} (ha : inWindow a) (hb : inWindow b) (hab : a ≠ b)
    (h13a : 13 ∣ a) (h13b : 13 ∣ b) :
    (¬(7 ∣ a) ∧ ¬(11 ∣ a)) ∨ (¬(7 ∣ b) ∧ ¬(11 ∣ b)) := by
  -- At most one of a, b can be 6006
  by_cases ha6 : a = 6006
  · -- a = 6006, so b ≠ 6006
    right
    have hb6 : b ≠ 6006 := by omega
    constructor
    · intro h7; exact hb6 (only_6006_is_special b hb h13b (Or.inl h7))
    · intro h11; exact hb6 (only_6006_is_special b hb h13b (Or.inr h11))
  · -- a ≠ 6006
    left
    constructor
    · intro h7; exact ha6 (only_6006_is_special a ha h13a (Or.inl h7))
    · intro h11; exact ha6 (only_6006_is_special a ha h13a (Or.inr h11))

/-! ## Main Theorem -/

theorem no_valid_triple (x y z : ℕ)
    (hx : inWindow x) (hy : inWindow y) (hz : inWindow z)
    (hxy : x < y) (hyz : y < z)
    (hdiv : 7^2 * 11^2 * 13^2 ∣ x * y * z) : False := by
  -- Basic facts
  have hxne : x ≠ 0 := by simp [inWindow] at hx; omega
  have hyne : y ≠ 0 := by simp [inWindow] at hy; omega
  have hzne : z ≠ 0 := by simp [inWindow] at hz; omega
  have hxyz : x * y * z ≠ 0 := by positivity

  -- Extract divisibility
  have h7sq : 7^2 ∣ x * y * z := Nat.dvd_trans ⟨11^2 * 13^2, by ring⟩ hdiv
  have h11sq : 11^2 ∣ x * y * z := Nat.dvd_trans ⟨7^2 * 13^2, by ring⟩ hdiv
  have h13sq : 13^2 ∣ x * y * z := Nat.dvd_trans ⟨7^2 * 11^2, by ring⟩ hdiv

  -- Convert to valuation bounds using our helper
  have hvp : vp x + vp y + vp z ≥ 2 := by
    have h := padicValNat_dvd_iff_le hxyz |>.mp h7sq
    rw [padicValNat_mul3 7 x y z hxne hyne hzne] at h; exact h
  have hvq : vq x + vq y + vq z ≥ 2 := by
    have h := padicValNat_dvd_iff_le hxyz |>.mp h11sq
    rw [padicValNat_mul3 11 x y z hxne hyne hzne] at h; exact h
  have hvr : vr x + vr y + vr z ≥ 2 := by
    have h := padicValNat_dvd_iff_le hxyz |>.mp h13sq
    rw [padicValNat_mul3 13 x y z hxne hyne hzne] at h; exact h

  -- Each vr ≤ 1
  have hvr_x := vr_le_one x hx
  have hvr_y := vr_le_one y hy
  have hvr_z := vr_le_one z hz

  -- Two of them have vr = 1
  have htwo := two_eq_one_of_sum_ge_two hvr_x hvr_y hvr_z hvr

  -- Helper lemmas
  have h7_of_vp : ∀ n, vp n ≥ 1 → 7 ∣ n := fun n h => dvd_of_one_le_padicValNat h
  have h11_of_vq : ∀ n, vq n ≥ 1 → 11 ∣ n := fun n h => dvd_of_one_le_padicValNat h
  have h13_of_vr : ∀ n, vr n ≥ 1 → 13 ∣ n := fun n h => dvd_of_one_le_padicValNat h
  have h77 : ∀ n, 7 ∣ n → 11 ∣ n → 77 ∣ n := fun n h7 h11 =>
    (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 7 11) h7 h11)

  -- The key argument: given two 13-divisible numbers, one is "pure 13",
  -- forcing the remaining numbers to carry all of vp and vq, which is impossible.
  rcases htwo with ⟨hvrx1, hvry1⟩ | ⟨hvrx1, hvrz1⟩ | ⟨hvry1, hvrz1⟩

  · -- x and y are divisible by 13
    have h13x : 13 ∣ x := h13_of_vr x (by omega)
    have h13y : 13 ∣ y := h13_of_vr y (by omega)
    -- One of them is pure 13 (not div by 7 or 11)
    have hpure := exists_pure13_of_two_div_13 hx hy (by omega) h13x h13y
    rcases hpure with ⟨hx_no7, hx_no11⟩ | ⟨hy_no7, hy_no11⟩
    · -- x is pure 13
      have hvpx : vp x = 0 := padicValNat.eq_zero_of_not_dvd hx_no7
      have hvqx : vq x = 0 := padicValNat.eq_zero_of_not_dvd hx_no11
      -- So vp y + vp z ≥ 2 and vq y + vq z ≥ 2
      have hvp_yz : vp y + vp z ≥ 2 := by omega
      have hvq_yz : vq y + vq z ≥ 2 := by omega
      -- Is y = 6006?
      by_cases hy6 : y = 6006
      · have hvpy : vp y = 1 := by subst hy6; native_decide
        have hvqy : vq y = 1 := by subst hy6; native_decide
        have hvpz : vp z ≥ 1 := by omega
        have hvqz : vq z ≥ 1 := by omega
        have h7z := h7_of_vp z hvpz
        have h11z := h11_of_vq z hvqz
        have h77z := h77 z h7z h11z
        have hz6 := only_6006_div_77 z hz h77z
        omega  -- y = z = 6006 but y < z
      · -- y ≠ 6006, so y is also pure 13
        have hy_no7 : ¬(7 ∣ y) := fun h => hy6 (only_6006_is_special y hy h13y (Or.inl h))
        have hy_no11 : ¬(11 ∣ y) := fun h => hy6 (only_6006_is_special y hy h13y (Or.inr h))
        have hvpy : vp y = 0 := padicValNat.eq_zero_of_not_dvd hy_no7
        have hvqy : vq y = 0 := padicValNat.eq_zero_of_not_dvd hy_no11
        -- z must have vp ≥ 2 and vq ≥ 2
        have hvpz : vp z ≥ 2 := by omega
        have hvqz : vq z ≥ 2 := by omega
        have h49z : 49 ∣ z := padicValNat_dvd_iff_le hzne |>.mpr hvpz
        have h121z : 121 ∣ z := padicValNat_dvd_iff_le hzne |>.mpr hvqz
        have h5929z : 5929 ∣ z := (by decide : Nat.Coprime 49 121).mul_dvd_of_dvd_of_dvd h49z h121z
        exact no_5929_in_window z hz h5929z
    · -- y is pure 13
      have hvpy : vp y = 0 := padicValNat.eq_zero_of_not_dvd hy_no7
      have hvqy : vq y = 0 := padicValNat.eq_zero_of_not_dvd hy_no11
      have hvp_xz : vp x + vp z ≥ 2 := by omega
      have hvq_xz : vq x + vq z ≥ 2 := by omega
      by_cases hx6 : x = 6006
      · have hvpx : vp x = 1 := by subst hx6; native_decide
        have hvqx : vq x = 1 := by subst hx6; native_decide
        have hvpz : vp z ≥ 1 := by omega
        have hvqz : vq z ≥ 1 := by omega
        have h7z := h7_of_vp z hvpz
        have h11z := h11_of_vq z hvqz
        have h77z := h77 z h7z h11z
        have hz6 := only_6006_div_77 z hz h77z
        omega
      · have hx_no7 : ¬(7 ∣ x) := fun h => hx6 (only_6006_is_special x hx h13x (Or.inl h))
        have hx_no11 : ¬(11 ∣ x) := fun h => hx6 (only_6006_is_special x hx h13x (Or.inr h))
        have hvpx : vp x = 0 := padicValNat.eq_zero_of_not_dvd hx_no7
        have hvqx : vq x = 0 := padicValNat.eq_zero_of_not_dvd hx_no11
        have hvpz : vp z ≥ 2 := by omega
        have hvqz : vq z ≥ 2 := by omega
        have h49z : 49 ∣ z := padicValNat_dvd_iff_le hzne |>.mpr hvpz
        have h121z : 121 ∣ z := padicValNat_dvd_iff_le hzne |>.mpr hvqz
        have h5929z : 5929 ∣ z := (by decide : Nat.Coprime 49 121).mul_dvd_of_dvd_of_dvd h49z h121z
        exact no_5929_in_window z hz h5929z

  · -- x and z are divisible by 13
    have h13x : 13 ∣ x := h13_of_vr x (by omega)
    have h13z : 13 ∣ z := h13_of_vr z (by omega)
    have hpure := exists_pure13_of_two_div_13 hx hz (by omega) h13x h13z
    rcases hpure with ⟨hx_no7, hx_no11⟩ | ⟨hz_no7, hz_no11⟩
    · have hvpx : vp x = 0 := padicValNat.eq_zero_of_not_dvd hx_no7
      have hvqx : vq x = 0 := padicValNat.eq_zero_of_not_dvd hx_no11
      have hvp_yz : vp y + vp z ≥ 2 := by omega
      have hvq_yz : vq y + vq z ≥ 2 := by omega
      by_cases hz6 : z = 6006
      · have hvpz : vp z = 1 := by subst hz6; native_decide
        have hvqz : vq z = 1 := by subst hz6; native_decide
        have hvpy : vp y ≥ 1 := by omega
        have hvqy : vq y ≥ 1 := by omega
        have h77y := h77 y (h7_of_vp y hvpy) (h11_of_vq y hvqy)
        have hy6 := only_6006_div_77 y hy h77y
        omega
      · have hz_no7 : ¬(7 ∣ z) := fun h => hz6 (only_6006_is_special z hz h13z (Or.inl h))
        have hz_no11 : ¬(11 ∣ z) := fun h => hz6 (only_6006_is_special z hz h13z (Or.inr h))
        have hvpz : vp z = 0 := padicValNat.eq_zero_of_not_dvd hz_no7
        have hvqz : vq z = 0 := padicValNat.eq_zero_of_not_dvd hz_no11
        have hvpy : vp y ≥ 2 := by omega
        have hvqy : vq y ≥ 2 := by omega
        have h49y : 49 ∣ y := padicValNat_dvd_iff_le hyne |>.mpr hvpy
        have h121y : 121 ∣ y := padicValNat_dvd_iff_le hyne |>.mpr hvqy
        have h5929y : 5929 ∣ y := (by decide : Nat.Coprime 49 121).mul_dvd_of_dvd_of_dvd h49y h121y
        exact no_5929_in_window y hy h5929y
    · have hvpz : vp z = 0 := padicValNat.eq_zero_of_not_dvd hz_no7
      have hvqz : vq z = 0 := padicValNat.eq_zero_of_not_dvd hz_no11
      have hvp_xy : vp x + vp y ≥ 2 := by omega
      have hvq_xy : vq x + vq y ≥ 2 := by omega
      by_cases hx6 : x = 6006
      · have hvpx : vp x = 1 := by subst hx6; native_decide
        have hvqx : vq x = 1 := by subst hx6; native_decide
        have hvpy : vp y ≥ 1 := by omega
        have hvqy : vq y ≥ 1 := by omega
        have h77y := h77 y (h7_of_vp y hvpy) (h11_of_vq y hvqy)
        have hy6 := only_6006_div_77 y hy h77y
        omega
      · have hx_no7 : ¬(7 ∣ x) := fun h => hx6 (only_6006_is_special x hx h13x (Or.inl h))
        have hx_no11 : ¬(11 ∣ x) := fun h => hx6 (only_6006_is_special x hx h13x (Or.inr h))
        have hvpx : vp x = 0 := padicValNat.eq_zero_of_not_dvd hx_no7
        have hvqx : vq x = 0 := padicValNat.eq_zero_of_not_dvd hx_no11
        have hvpy : vp y ≥ 2 := by omega
        have hvqy : vq y ≥ 2 := by omega
        have h49y : 49 ∣ y := padicValNat_dvd_iff_le hyne |>.mpr hvpy
        have h121y : 121 ∣ y := padicValNat_dvd_iff_le hyne |>.mpr hvqy
        have h5929y : 5929 ∣ y := (by decide : Nat.Coprime 49 121).mul_dvd_of_dvd_of_dvd h49y h121y
        exact no_5929_in_window y hy h5929y

  · -- y and z are divisible by 13
    have h13y : 13 ∣ y := h13_of_vr y (by omega)
    have h13z : 13 ∣ z := h13_of_vr z (by omega)
    have hpure := exists_pure13_of_two_div_13 hy hz (by omega) h13y h13z
    rcases hpure with ⟨hy_no7, hy_no11⟩ | ⟨hz_no7, hz_no11⟩
    · have hvpy : vp y = 0 := padicValNat.eq_zero_of_not_dvd hy_no7
      have hvqy : vq y = 0 := padicValNat.eq_zero_of_not_dvd hy_no11
      have hvp_xz : vp x + vp z ≥ 2 := by omega
      have hvq_xz : vq x + vq z ≥ 2 := by omega
      by_cases hz6 : z = 6006
      · have hvpz : vp z = 1 := by subst hz6; native_decide
        have hvqz : vq z = 1 := by subst hz6; native_decide
        have hvpx : vp x ≥ 1 := by omega
        have hvqx : vq x ≥ 1 := by omega
        have h77x := h77 x (h7_of_vp x hvpx) (h11_of_vq x hvqx)
        have hx6 := only_6006_div_77 x hx h77x
        omega
      · have hz_no7 : ¬(7 ∣ z) := fun h => hz6 (only_6006_is_special z hz h13z (Or.inl h))
        have hz_no11 : ¬(11 ∣ z) := fun h => hz6 (only_6006_is_special z hz h13z (Or.inr h))
        have hvpz : vp z = 0 := padicValNat.eq_zero_of_not_dvd hz_no7
        have hvqz : vq z = 0 := padicValNat.eq_zero_of_not_dvd hz_no11
        have hvpx : vp x ≥ 2 := by omega
        have hvqx : vq x ≥ 2 := by omega
        have h49x : 49 ∣ x := padicValNat_dvd_iff_le hxne |>.mpr hvpx
        have h121x : 121 ∣ x := padicValNat_dvd_iff_le hxne |>.mpr hvqx
        have h5929x : 5929 ∣ x := (by decide : Nat.Coprime 49 121).mul_dvd_of_dvd_of_dvd h49x h121x
        exact no_5929_in_window x hx h5929x
    · have hvpz : vp z = 0 := padicValNat.eq_zero_of_not_dvd hz_no7
      have hvqz : vq z = 0 := padicValNat.eq_zero_of_not_dvd hz_no11
      have hvp_xy : vp x + vp y ≥ 2 := by omega
      have hvq_xy : vq x + vq y ≥ 2 := by omega
      by_cases hy6 : y = 6006
      · have hvpy : vp y = 1 := by subst hy6; native_decide
        have hvqy : vq y = 1 := by subst hy6; native_decide
        have hvpx : vp x ≥ 1 := by omega
        have hvqx : vq x ≥ 1 := by omega
        have h77x := h77 x (h7_of_vp x hvpx) (h11_of_vq x hvqx)
        have hx6 := only_6006_div_77 x hx h77x
        omega
      · have hy_no7 : ¬(7 ∣ y) := fun h => hy6 (only_6006_is_special y hy h13y (Or.inl h))
        have hy_no11 : ¬(11 ∣ y) := fun h => hy6 (only_6006_is_special y hy h13y (Or.inr h))
        have hvpy : vp y = 0 := padicValNat.eq_zero_of_not_dvd hy_no7
        have hvqy : vq y = 0 := padicValNat.eq_zero_of_not_dvd hy_no11
        have hvpx : vp x ≥ 2 := by omega
        have hvqx : vq x ≥ 2 := by omega
        have h49x : 49 ∣ x := padicValNat_dvd_iff_le hxne |>.mpr hvpx
        have h121x : 121 ∣ x := padicValNat_dvd_iff_le hxne |>.mpr hvqx
        have h5929x : 5929 ∣ x := (by decide : Nat.Coprime 49 121).mul_dvd_of_dvd_of_dvd h49x h121x
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
