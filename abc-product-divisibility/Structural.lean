/-
# Structural Core: The Pure Proof Without Concrete Numbers

This file proves the structural lemma that underlies all counterexamples of the form
(a, b, c) = (pq, pr, qr) for primes p, q, r.

The key insight: if a window W satisfies properties A/B/C/D, then no valid triple exists.

## Window Properties

Given primes p, q, r and a window predicate W:

**(A) No r² in the window**: ∀ x ∈ W, ¬(r² ∣ x)
**(B) Unique multi-prime for r**: ∀ x ∈ W, (r ∣ x ∧ (p ∣ x ∨ q ∣ x)) → x = N
**(C) Unique pq-multiple**: ∀ x ∈ W, (pq ∣ x) → x = N
**(D) N has single copies**: p² ∤ N, q² ∤ N, r² ∤ N

The structural contradiction:
1. Need r² ∣ xyz, but no single number has r², so two numbers must have r
2. Among r-multiples, at most one (N) can also have p or q
3. So the "other" r-multiple is "pure r" - contributes no p or q
4. The third number must supply all of p² and q² → needs pq ∣ it → must be N
5. Contradiction: N can't be both the multi-prime r-multiple AND the third number
-/

import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-! ## Valuation Helpers -/

/-- Triple product valuation -/
lemma padicValNat_mul3 (p x y z : ℕ) [Fact (Nat.Prime p)] (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    padicValNat p (x * y * z) = padicValNat p x + padicValNat p y + padicValNat p z := by
  rw [padicValNat.mul (mul_ne_zero hx hy) hz, padicValNat.mul hx hy]

/-- If sum of three values each ≤ 1 is ≥ 2, then two of them equal 1 -/
lemma two_eq_one_of_sum_ge_two {a b c : ℕ} (ha : a ≤ 1) (hb : b ≤ 1) (hc : c ≤ 1)
    (hsum : a + b + c ≥ 2) : (a = 1 ∧ b = 1) ∨ (a = 1 ∧ c = 1) ∨ (b = 1 ∧ c = 1) := by
  omega

/-! ## Window Properties Structure -/

/-- The four properties that a window must satisfy for the structural proof to work -/
structure WindowProps (p q r : ℕ) (inWindow : ℕ → Prop) (N : ℕ) where
  hp : Fact (Nat.Prime p)
  hq : Fact (Nat.Prime q)
  hr : Fact (Nat.Prime r)
  /-- p and q are distinct primes -/
  hpq_ne : p ≠ q
  /-- (A) No r² in window -/
  no_r_squared : ∀ x, inWindow x → ¬(r^2 ∣ x)
  /-- (B) Unique multi-prime: if r ∣ x and (p ∣ x or q ∣ x), then x = N -/
  unique_multi_r : ∀ x, inWindow x → r ∣ x → (p ∣ x ∨ q ∣ x) → x = N
  /-- (C) Unique pq-multiple: if pq ∣ x, then x = N -/
  unique_pq : ∀ x, inWindow x → p * q ∣ x → x = N
  /-- N is in the window -/
  N_in_window : inWindow N
  /-- (D) N has only single copies of each prime -/
  N_no_p_squared : ¬(p^2 ∣ N)
  N_no_q_squared : ¬(q^2 ∣ N)
  N_no_r_squared : ¬(r^2 ∣ N)
  /-- Window elements are positive -/
  window_pos : ∀ x, inWindow x → 0 < x

/-! ## DRY Helper Lemmas for the Main Proof -/

namespace WindowProps

variable {p q r : ℕ} {inWindow : ℕ → Prop} {N : ℕ}

/-- N is nonzero (from window_pos) -/
lemma N_ne_zero (W : WindowProps p q r inWindow N) : N ≠ 0 :=
  Nat.pos_iff_ne_zero.mp (W.window_pos N W.N_in_window)

/-- If n = N, then vp n ≤ 1 (Property D for p) -/
lemma vp_le_one_of_eq_N (W : WindowProps p q r inWindow N) (n : ℕ) (hnN : n = N) :
    padicValNat p n ≤ 1 := by
  haveI := W.hp
  have hNne : N ≠ 0 := W.N_ne_zero
  by_contra h; push_neg at h
  have hp2 : p^2 ∣ n := padicValNat_dvd_iff_le (hnN ▸ hNne) |>.mpr h
  rw [hnN] at hp2
  exact W.N_no_p_squared hp2

/-- If n = N, then vq n ≤ 1 (Property D for q) -/
lemma vq_le_one_of_eq_N (W : WindowProps p q r inWindow N) (n : ℕ) (hnN : n = N) :
    padicValNat q n ≤ 1 := by
  haveI := W.hq
  have hNne : N ≠ 0 := W.N_ne_zero
  by_contra h; push_neg at h
  have hq2 : q^2 ∣ n := padicValNat_dvd_iff_le (hnN ▸ hNne) |>.mpr h
  rw [hnN] at hq2
  exact W.N_no_q_squared hq2

/-- If n ≠ N and r ∣ n and n is in window, then n is "pure r" (¬p ∣ n ∧ ¬q ∣ n) -/
lemma pure_r_of_ne_N (W : WindowProps p q r inWindow N)
    (n : ℕ) (hn : inWindow n) (hr_n : r ∣ n) (hnN : n ≠ N) :
    ¬(p ∣ n) ∧ ¬(q ∣ n) := by
  constructor
  · intro hp_n; exact hnN (W.unique_multi_r n hn hr_n (Or.inl hp_n))
  · intro hq_n; exact hnN (W.unique_multi_r n hn hr_n (Or.inr hq_n))

/-- Among two r-multiples in the window, at least one is "pure r" (not divisible by p or q) -/
lemma exists_pure_r (W : WindowProps p q r inWindow N)
    {a b : ℕ} (ha : inWindow a) (hb : inWindow b) (hab : a ≠ b)
    (hra : r ∣ a) (hrb : r ∣ b) :
    (¬(p ∣ a) ∧ ¬(q ∣ a)) ∨ (¬(p ∣ b) ∧ ¬(q ∣ b)) := by
  by_cases haN : a = N
  · right; exact W.pure_r_of_ne_N b hb hrb (by omega)
  · left; exact W.pure_r_of_ne_N a ha hra haN

/-- pq divides n if both p and q divide n (using coprimality of distinct primes) -/
lemma pq_dvd_of_p_dvd_q_dvd (W : WindowProps p q r inWindow N)
    (n : ℕ) (hp_n : p ∣ n) (hq_n : q ∣ n) : p * q ∣ n := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes W.hp.out W.hq.out).mpr W.hpq_ne
  exact hcop.mul_dvd_of_dvd_of_dvd hp_n hq_n

/-- Core contradiction: if vp ≥ 2 and vq ≥ 2 for some n in window, then n = N, contradicting N_no_p_squared -/
lemma contradiction_of_vp_ge_2_vq_ge_2 (W : WindowProps p q r inWindow N)
    (n : ℕ) (hn : inWindow n) (hne : n ≠ 0)
    (hvp : padicValNat p n ≥ 2) (hvq : padicValNat q n ≥ 2) : False := by
  haveI := W.hp
  haveI := W.hq
  have hp2 : p^2 ∣ n := padicValNat_dvd_iff_le hne |>.mpr hvp
  have hq2 : q^2 ∣ n := padicValNat_dvd_iff_le hne |>.mpr hvq
  have hp_n : p ∣ n := Nat.dvd_trans ⟨p, by ring⟩ hp2
  have hq_n : q ∣ n := Nat.dvd_trans ⟨q, by ring⟩ hq2
  have hpq_n := W.pq_dvd_of_p_dvd_q_dvd n hp_n hq_n
  have hnN := W.unique_pq n hn hpq_n
  rw [hnN] at hp2
  exact W.N_no_p_squared hp2

end WindowProps

/-! ## The Main Structural Theorem -/

/-- The main structural theorem: no valid triple exists in a window with properties A/B/C/D -/
theorem no_valid_triple_of_window_props {p q r : ℕ} {inWindow : ℕ → Prop} {N : ℕ}
    (W : WindowProps p q r inWindow N)
    (x y z : ℕ)
    (hx : inWindow x) (hy : inWindow y) (hz : inWindow z)
    (hxy : x < y) (hyz : y < z)
    (hdiv : p^2 * q^2 * r^2 ∣ x * y * z) : False := by
  haveI := W.hp
  haveI := W.hq
  haveI := W.hr

  -- Basic non-zero facts (from window_pos)
  have hxne : x ≠ 0 := Nat.pos_iff_ne_zero.mp (W.window_pos x hx)
  have hyne : y ≠ 0 := Nat.pos_iff_ne_zero.mp (W.window_pos y hy)
  have hzne : z ≠ 0 := Nat.pos_iff_ne_zero.mp (W.window_pos z hz)
  have hxyz : x * y * z ≠ 0 := by positivity
  have hNne : N ≠ 0 := W.N_ne_zero

  -- Abbreviations for valuations
  let vp := padicValNat p
  let vq := padicValNat q
  let vr := padicValNat r

  -- Extract divisibility by each prime squared and convert to valuation bounds
  have hvp : vp x + vp y + vp z ≥ 2 := by
    have hp_sq : p^2 ∣ x * y * z := Nat.dvd_trans ⟨q^2 * r^2, by ring⟩ hdiv
    have h := padicValNat_dvd_iff_le hxyz |>.mp hp_sq
    rw [padicValNat_mul3 p x y z hxne hyne hzne] at h; exact h
  have hvq : vq x + vq y + vq z ≥ 2 := by
    have hq_sq : q^2 ∣ x * y * z := Nat.dvd_trans ⟨p^2 * r^2, by ring⟩ hdiv
    have h := padicValNat_dvd_iff_le hxyz |>.mp hq_sq
    rw [padicValNat_mul3 q x y z hxne hyne hzne] at h; exact h
  have hvr : vr x + vr y + vr z ≥ 2 := by
    have hr_sq : r^2 ∣ x * y * z := Nat.dvd_trans ⟨p^2 * q^2, by ring⟩ hdiv
    have h := padicValNat_dvd_iff_le hxyz |>.mp hr_sq
    rw [padicValNat_mul3 r x y z hxne hyne hzne] at h; exact h

  -- Property (A): vr ≤ 1 for each number (no r² in window)
  have hvr_le : ∀ n, inWindow n → n ≠ 0 → vr n ≤ 1 := fun n hn hne => by
    by_contra h; push_neg at h
    exact W.no_r_squared n hn (padicValNat_dvd_iff_le hne |>.mpr h)
  have hvr_x : vr x ≤ 1 := hvr_le x hx hxne
  have hvr_y : vr y ≤ 1 := hvr_le y hy hyne
  have hvr_z : vr z ≤ 1 := hvr_le z hz hzne

  -- Two of {x, y, z} have vr = 1 (i.e., are divisible by r)
  have htwo := two_eq_one_of_sum_ge_two hvr_x hvr_y hvr_z hvr

  -- Helper to get divisibility from valuation
  have dvd_of_vr_ge_1 : ∀ n, vr n ≥ 1 → r ∣ n := fun n h => dvd_of_one_le_padicValNat h
  have dvd_of_vp_ge_1 : ∀ n, vp n ≥ 1 → p ∣ n := fun n h => dvd_of_one_le_padicValNat h
  have dvd_of_vq_ge_1 : ∀ n, vq n ≥ 1 → q ∣ n := fun n h => dvd_of_one_le_padicValNat h

  -- Helper: valuation is 0 if prime doesn't divide
  have vp_zero_of_not_dvd : ∀ n, ¬(p ∣ n) → vp n = 0 := fun n h => padicValNat.eq_zero_of_not_dvd h
  have vq_zero_of_not_dvd : ∀ n, ¬(q ∣ n) → vq n = 0 := fun n h => padicValNat.eq_zero_of_not_dvd h

  /-
  The proof strategy for each case:
  - Two numbers (say a, b) are r-multiples with vr = 1
  - One of them is "pure r" (doesn't have p or q), contributing vp = vq = 0
  - Either the other r-multiple is N (bounded by property D), or it's also pure r
  - If one is N: third number needs vp ≥ 1 and vq ≥ 1 → pq divides it → it's N → contradiction
  - If both pure: third number needs vp ≥ 2 and vq ≥ 2 → p² divides it → it's N → but p² ∤ N
  -/

  -- Unified handler for when we have a pure r number and need to analyze another
  have handle_pure_and_potential_N :
      ∀ (pure other third : ℕ),
        inWindow pure → inWindow other → inWindow third →
        pure ≠ 0 → other ≠ 0 → third ≠ 0 →
        pure ≠ other → pure ≠ third → other ≠ third →
        r ∣ other →
        vp pure = 0 → vq pure = 0 →
        vp pure + vp other + vp third ≥ 2 →
        vq pure + vq other + vq third ≥ 2 →
        False := fun pure other third h_pure h_other h_third hpure_ne hother_ne hthird_ne
                     hne1 hne2 hne3 hr_other hvp_pure hvq_pure hvp_sum hvq_sum => by
    -- other + third must supply vp ≥ 2 and vq ≥ 2
    have hvp_ot : vp other + vp third ≥ 2 := by omega
    have hvq_ot : vq other + vq third ≥ 2 := by omega
    by_cases hotherN : other = N
    · -- other = N, so vp other ≤ 1 and vq other ≤ 1 by property D
      have hvp_other_le : vp other ≤ 1 := W.vp_le_one_of_eq_N other hotherN
      have hvq_other_le : vq other ≤ 1 := W.vq_le_one_of_eq_N other hotherN
      -- third must have vp ≥ 1 and vq ≥ 1
      have hvp_third : vp third ≥ 1 := by omega
      have hvq_third : vq third ≥ 1 := by omega
      have hp_third := dvd_of_vp_ge_1 third hvp_third
      have hq_third := dvd_of_vq_ge_1 third hvq_third
      have hpq_third := W.pq_dvd_of_p_dvd_q_dvd third hp_third hq_third
      have hthirdN := W.unique_pq third h_third hpq_third
      -- But other = N and third = N contradicts other ≠ third
      omega
    · -- other ≠ N, so other is also pure r
      have ⟨hother_no_p, hother_no_q⟩ := W.pure_r_of_ne_N other h_other hr_other hotherN
      have hvp_other := vp_zero_of_not_dvd other hother_no_p
      have hvq_other := vq_zero_of_not_dvd other hother_no_q
      -- third must have vp ≥ 2 and vq ≥ 2
      have hvp_third : vp third ≥ 2 := by omega
      have hvq_third : vq third ≥ 2 := by omega
      exact W.contradiction_of_vp_ge_2_vq_ge_2 third h_third hthird_ne hvp_third hvq_third

  -- Case analysis on which two have vr = 1
  rcases htwo with ⟨hvrx1, hvry1⟩ | ⟨hvrx1, hvrz1⟩ | ⟨hvry1, hvrz1⟩

  · -- x and y are divisible by r
    have hr_x : r ∣ x := dvd_of_vr_ge_1 x (by omega)
    have hr_y : r ∣ y := dvd_of_vr_ge_1 y (by omega)
    rcases W.exists_pure_r hx hy (by omega) hr_x hr_y with ⟨hx_no_p, hx_no_q⟩ | ⟨hy_no_p, hy_no_q⟩
    · -- x is pure r
      exact handle_pure_and_potential_N x y z hx hy hz hxne hyne hzne
        (by omega) (by omega) (by omega) hr_y
        (vp_zero_of_not_dvd x hx_no_p) (vq_zero_of_not_dvd x hx_no_q) hvp hvq
    · -- y is pure r
      exact handle_pure_and_potential_N y x z hy hx hz hyne hxne hzne
        (by omega) (by omega) (by omega) hr_x
        (vp_zero_of_not_dvd y hy_no_p) (vq_zero_of_not_dvd y hy_no_q)
        (by omega : vp y + vp x + vp z ≥ 2) (by omega : vq y + vq x + vq z ≥ 2)

  · -- x and z are divisible by r
    have hr_x : r ∣ x := dvd_of_vr_ge_1 x (by omega)
    have hr_z : r ∣ z := dvd_of_vr_ge_1 z (by omega)
    rcases W.exists_pure_r hx hz (by omega) hr_x hr_z with ⟨hx_no_p, hx_no_q⟩ | ⟨hz_no_p, hz_no_q⟩
    · -- x is pure r
      exact handle_pure_and_potential_N x z y hx hz hy hxne hzne hyne
        (by omega) (by omega) (by omega) hr_z
        (vp_zero_of_not_dvd x hx_no_p) (vq_zero_of_not_dvd x hx_no_q)
        (by omega : vp x + vp z + vp y ≥ 2) (by omega : vq x + vq z + vq y ≥ 2)
    · -- z is pure r
      exact handle_pure_and_potential_N z x y hz hx hy hzne hxne hyne
        (by omega) (by omega) (by omega) hr_x
        (vp_zero_of_not_dvd z hz_no_p) (vq_zero_of_not_dvd z hz_no_q)
        (by omega : vp z + vp x + vp y ≥ 2) (by omega : vq z + vq x + vq y ≥ 2)

  · -- y and z are divisible by r
    have hr_y : r ∣ y := dvd_of_vr_ge_1 y (by omega)
    have hr_z : r ∣ z := dvd_of_vr_ge_1 z (by omega)
    rcases W.exists_pure_r hy hz (by omega) hr_y hr_z with ⟨hy_no_p, hy_no_q⟩ | ⟨hz_no_p, hz_no_q⟩
    · -- y is pure r
      exact handle_pure_and_potential_N y z x hy hz hx hyne hzne hxne
        (by omega) (by omega) (by omega) hr_z
        (vp_zero_of_not_dvd y hy_no_p) (vq_zero_of_not_dvd y hy_no_q)
        (by omega : vp y + vp z + vp x ≥ 2) (by omega : vq y + vq z + vq x ≥ 2)
    · -- z is pure r
      exact handle_pure_and_potential_N z y x hz hy hx hzne hyne hxne
        (by omega) (by omega) (by omega) hr_y
        (vp_zero_of_not_dvd z hz_no_p) (vq_zero_of_not_dvd z hz_no_q)
        (by omega : vp z + vp y + vp x ≥ 2) (by omega : vq z + vq y + vq x ≥ 2)
