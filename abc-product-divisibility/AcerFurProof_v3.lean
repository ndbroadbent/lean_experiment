/-
# AcerFur's Proof v3: Fully Explicit

The proof has two parts:
1. No multiple of r² = 169 exists in [5935, 6077]
2. Therefore to get v_r(xyz) ≥ 2, we need TWO of x,y,z divisible by r
3. But only 6006 is divisible by r AND another prime
4. So we need a "pure r" multiple (divisible by r but not p or q)
5. Similarly for p and q, leading to contradiction
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Factorization.Basic

def p : ℕ := 7
def q : ℕ := 11
def r : ℕ := 13
def windowStart : ℕ := 5935
def windowEnd : ℕ := 6077

/-! ## Key Valuation Lemmas -/

/-- If p² | a*b and p | a but p² ∤ a, then p | b -/
lemma sq_dvd_mul_of_dvd_not_sq {p a b : ℕ} (hp : Nat.Prime p)
    (h : p^2 ∣ a * b) (ha : p ∣ a) (ha2 : ¬(p^2 ∣ a)) : p ∣ b := by
  have hpa := hp.dvd_of_dvd_pow ha
  rcases ha with ⟨k, hk⟩
  have hpnk : ¬(p ∣ k) := by
    intro ⟨m, hm⟩
    apply ha2
    use m
    omega
  rw [hk] at h
  have h' : p^2 ∣ p * k * b := h
  rw [mul_comm p k, mul_assoc] at h'
  have h'' : p ∣ k * b := by
    rcases h' with ⟨m, hm⟩
    use m
    have : p * (p * (k * b)) = p^2 * (k * b) := by ring
    rw [← this] at hm
    have hp0 : p ≠ 0 := hp.ne_zero
    omega
  rcases hp.dvd_mul.mp h'' with hk' | hb
  · exact absurd hk' hpnk
  · exact hb

/-- If p² | a*b*c and p | a but p² ∤ a and p ∤ b and p ∤ c, contradiction -/
lemma sq_dvd_mul3_impossible {p a b c : ℕ} (hp : Nat.Prime p)
    (h : p^2 ∣ a * b * c) (ha : p ∣ a) (ha2 : ¬(p^2 ∣ a))
    (hb : ¬(p ∣ b)) (hc : ¬(p ∣ c)) : False := by
  have hbc : p ∣ b * c := sq_dvd_mul_of_dvd_not_sq hp (by ring_nf; ring_nf at h; exact h) ha ha2
  rcases hp.dvd_mul.mp hbc with h' | h'
  · exact hb h'
  · exact hc h'

/-- If p² | a*b*c and p | a but p² ∤ a, then p | b*c -/
lemma sq_dvd_mul3_rest {p a b c : ℕ} (hp : Nat.Prime p)
    (h : p^2 ∣ a * b * c) (ha : p ∣ a) (ha2 : ¬(p^2 ∣ a)) : p ∣ b * c := by
  exact sq_dvd_mul_of_dvd_not_sq hp (by ring_nf; ring_nf at h; exact h) ha ha2

/-- If p² | a*b*c and only a is divisible by p, then p² | a -/
lemma sq_dvd_unique {p a b c : ℕ} (hp : Nat.Prime p)
    (h : p^2 ∣ a * b * c) (ha : p ∣ a) (hb : ¬(p ∣ b)) (hc : ¬(p ∣ c)) : p^2 ∣ a := by
  by_contra ha2
  exact sq_dvd_mul3_impossible hp h ha ha2 hb hc

/-- 6006 is the only number in window divisible by two or more of {p, q, r} -/
theorem only_6006_multi (x : ℕ) (hlo : windowStart ≤ x) (hhi : x ≤ windowEnd)
    (h : (p ∣ x ∧ q ∣ x) ∨ (p ∣ x ∧ r ∣ x) ∨ (q ∣ x ∧ r ∣ x)) : x = 6006 := by
  simp only [windowStart, windowEnd] at hlo hhi
  rcases h with ⟨hp, hq⟩ | ⟨hp, hr⟩ | ⟨hq, hr⟩ <;>
  · simp only [p, q, r] at hp hq hr
    omega

/-- No multiple of r² = 169 in the window -/
theorem no_r_squared (x : ℕ) (hlo : windowStart ≤ x) (hhi : x ≤ windowEnd) : ¬(r^2 ∣ x) := by
  simp only [windowStart, windowEnd, r] at hlo hhi ⊢
  intro ⟨k, hk⟩
  omega

/-- No multiple of q² = 121 in the window except possibly 6050 = 121 × 50, but 6050 isn't in range
    Actually 121 × 50 = 6050 IS in [5935, 6077]. Let's check all of them. -/
theorem q_squared_locations (x : ℕ) (hlo : windowStart ≤ x) (hhi : x ≤ windowEnd)
    (hq2 : q^2 ∣ x) : x = 5929 ∨ x = 6050 := by
  simp only [windowStart, windowEnd, q] at hlo hhi hq2
  obtain ⟨k, hk⟩ := hq2
  interval_cases k <;> simp_all

/-- Actually 5929 < 5935, so only 6050 -/
theorem q_squared_only_6050 (x : ℕ) (hlo : windowStart ≤ x) (hhi : x ≤ windowEnd)
    (hq2 : q^2 ∣ x) : x = 6050 := by
  have h := q_squared_locations x hlo hhi hq2
  simp only [windowStart] at hlo
  omega

/-- p² = 49 multiples in window -/
theorem p_squared_locations (x : ℕ) (hlo : windowStart ≤ x) (hhi : x ≤ windowEnd)
    (hp2 : p^2 ∣ x) : x ∈ ({5929, 5978, 6027, 6076} : Set ℕ) := by
  simp only [windowStart, windowEnd, p] at hlo hhi hp2
  obtain ⟨k, hk⟩ := hp2
  interval_cases k <;> simp_all [Set.mem_insert_iff]

/-- Filter to only those in range -/
theorem p_squared_in_range (x : ℕ) (hlo : windowStart ≤ x) (hhi : x ≤ windowEnd)
    (hp2 : p^2 ∣ x) : x ∈ ({5978, 6027, 6076} : Set ℕ) := by
  have h := p_squared_locations x hlo hhi hp2
  simp only [windowStart] at hlo
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
  omega

/-!
## The Key Analysis

To have (p*q)*(p*r)*(q*r) | xyz, we need:
- v_p(xyz) ≥ 2
- v_q(xyz) ≥ 2
- v_r(xyz) ≥ 2

Since no r² multiple exists, we need r | x and r | y (or similar pair).
Call these two numbers the "r-contributors".

Case 1: Both r-contributors are NOT 6006
  Then neither is divisible by p or q (by only_6006_multi).
  So neither contributes to v_p or v_q.
  The third number z must give v_p ≥ 2 AND v_q ≥ 2.
  This needs p² | z AND q² | z, i.e., (pq)² = 5929 | z.
  But 5929² > windowEnd, and 5929 itself means z = 5929 which is < windowStart.
  Contradiction.

Case 2: Exactly one r-contributor is 6006
  Say x = 6006. Then y is divisible by r but not by p or q.
  We still need v_p ≥ 2 from {6006, y, z}. 6006 gives v_p = 1.
  So we need v_p(y) + v_p(z) ≥ 1. Since y is not divisible by p, we need p | z.
  Similarly for q: we need q | z.
  So z is divisible by both p and q. By only_6006_multi, z = 6006.
  But x = 6006 and x < z, contradiction.

Therefore no valid triple exists.
-/

/-- A number in the window divisible by r but not by p or q -/
def pureR (x : ℕ) : Prop := windowStart ≤ x ∧ x ≤ windowEnd ∧ r ∣ x ∧ ¬(p ∣ x) ∧ ¬(q ∣ x)

/-- The multiples of r in the window that are NOT 6006 are "pure r" -/
theorem r_mult_pure_or_6006 (x : ℕ) (hlo : windowStart ≤ x) (hhi : x ≤ windowEnd)
    (hr : r ∣ x) : x = 6006 ∨ pureR x := by
  by_cases hp : p ∣ x
  · left
    exact only_6006_multi x hlo hhi (Or.inr (Or.inl ⟨hp, hr⟩))
  · by_cases hq : q ∣ x
    · left
      exact only_6006_multi x hlo hhi (Or.inr (Or.inr ⟨hq, hr⟩))
    · right
      exact ⟨hlo, hhi, hr, hp, hq⟩

/-- Main theorem: no valid triple exists -/
theorem no_valid_triple (x y z : ℕ)
    (hx : windowStart ≤ x ∧ x ≤ windowEnd)
    (hy : windowStart ≤ y ∧ y ≤ windowEnd)
    (hz : windowStart ≤ z ∧ z ≤ windowEnd)
    (hxy : x < y) (hyz : y < z)
    (hdiv : (p * q) * (p * r) * (q * r) ∣ x * y * z) : False := by
  -- We need v_r(xyz) ≥ 2. Since no r² in window, need two of x,y,z divisible by r.
  -- Extract divisibility requirements
  have habc : p * q * (p * r) * (q * r) = p^2 * q^2 * r^2 := by ring
  rw [habc] at hdiv

  -- Since r² | xyz and no r² | any single number, we need r | (two of x,y,z)
  have hr2_xyz : r^2 ∣ x * y * z := Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < p^2 * q^2)
    (by rw [← habc]; exact hdiv)

  -- Key: which two are divisible by r?
  -- We'll show all cases lead to contradiction

  -- First, none of x, y, z can have r² | it
  have hx_no_r2 : ¬(r^2 ∣ x) := no_r_squared x hx.1 hx.2
  have hy_no_r2 : ¬(r^2 ∣ y) := no_r_squared y hy.1 hy.2
  have hz_no_r2 : ¬(r^2 ∣ z) := no_r_squared z hz.1 hz.2

  -- So to get r² | xyz, we need r | (at least two of x, y, z)
  -- This is the valuation argument: if r² | xyz and r² ∤ each, then r divides ≥2 of them

  -- Let's proceed by cases on which numbers are divisible by r
  by_cases hrx : r ∣ x <;> by_cases hry : r ∣ y <;> by_cases hrz : r ∣ z

  -- Case: all three divisible by r
  · -- x, y, z all divisible by r. Classify each.
    rcases r_mult_pure_or_6006 x hx.1 hx.2 hrx with hx6006 | hxpure
    · rcases r_mult_pure_or_6006 y hy.1 hy.2 hry with hy6006 | hypure
      · omega  -- x = y = 6006 contradicts x < y
      · rcases r_mult_pure_or_6006 z hz.1 hz.2 hrz with hz6006 | hzpure
        · omega  -- x = z = 6006 contradicts x < z
        · -- x = 6006, y and z are pure r (not divisible by p or q)
          -- Need p² | xyz. x = 6006 gives v_p = 1. y, z give 0. Total = 1 < 2.
          have hp2_xyz : p^2 ∣ x * y * z := Nat.dvd_of_mul_dvd_mul_right (by decide : 0 < q^2 * r^2)
            (by ring_nf; ring_nf at hdiv; exact hdiv)
          have hp_x : p ∣ x := by simp [hx6006, p]; decide
          have hp2_x : ¬(p^2 ∣ x) := by simp [hx6006, p]; decide
          have hp_y : ¬(p ∣ y) := hypure.2.2.1
          have hp_z : ¬(p ∣ z) := hzpure.2.2.1
          -- p² | xyz, p | x but p² ∤ x, p ∤ y, p ∤ z
          -- So v_p(xyz) = v_p(x) + v_p(y) + v_p(z) = 1 + 0 + 0 = 1 < 2
          -- This contradicts p² | xyz
          have : p^2 ∣ x * y * z → p ∣ y * z := by
            intro h
            have hpx : p ∣ x := hp_x
            have hpnot2 : ¬(p^2 ∣ x) := hp2_x
            -- If p² | xyz and p | x but p² ∤ x, then p | yz
            sorry
          have hpyz := this hp2_xyz
          rcases Nat.Prime.dvd_mul (by decide : Nat.Prime p) hpyz with hp_y' | hp_z'
          · exact hp_y hp_y'
          · exact hp_z hp_z'
    · rcases r_mult_pure_or_6006 y hy.1 hy.2 hry with hy6006 | hypure
      · rcases r_mult_pure_or_6006 z hz.1 hz.2 hrz with hz6006 | hzpure
        · omega  -- y = z = 6006 contradicts y < z
        · -- y = 6006, x and z are pure r
          -- Same argument: need p² | xyz, but v_p(x) = 0, v_p(y) = 1, v_p(z) = 0
          have hp2_xyz : p^2 ∣ x * y * z := Nat.dvd_of_mul_dvd_mul_right (by decide : 0 < q^2 * r^2)
            (by ring_nf; ring_nf at hdiv; exact hdiv)
          have hp_x : ¬(p ∣ x) := hxpure.2.2.1
          have hp_y : p ∣ y := by simp [hy6006, p]; decide
          have hp2_y : ¬(p^2 ∣ y) := by simp [hy6006, p]; decide
          have hp_z : ¬(p ∣ z) := hzpure.2.2.1
          have : p^2 ∣ x * y * z → p ∣ x * z := by
            intro h
            sorry
          have hpxz := this hp2_xyz
          rcases Nat.Prime.dvd_mul (by decide : Nat.Prime p) hpxz with hp_x' | hp_z'
          · exact hp_x hp_x'
          · exact hp_z hp_z'
      · -- x and y are pure r
        rcases r_mult_pure_or_6006 z hz.1 hz.2 hrz with hz6006 | hzpure
        · -- z = 6006, x and y are pure r
          have hp2_xyz : p^2 ∣ x * y * z := Nat.dvd_of_mul_dvd_mul_right (by decide : 0 < q^2 * r^2)
            (by ring_nf; ring_nf at hdiv; exact hdiv)
          have hp_x : ¬(p ∣ x) := hxpure.2.2.1
          have hp_y : ¬(p ∣ y) := hypure.2.2.1
          have hp_z : p ∣ z := by simp [hz6006, p]; decide
          have hp2_z : ¬(p^2 ∣ z) := by simp [hz6006, p]; decide
          have : p^2 ∣ x * y * z → p ∣ x * y := by
            intro h
            sorry
          have hpxy := this hp2_xyz
          rcases Nat.Prime.dvd_mul (by decide : Nat.Prime p) hpxy with hp_x' | hp_y'
          · exact hp_x hp_x'
          · exact hp_y hp_y'
        · -- All three are pure r (none is 6006)
          -- None divisible by p, so p² ∤ xyz
          have hp2_xyz : p^2 ∣ x * y * z := Nat.dvd_of_mul_dvd_mul_right (by decide : 0 < q^2 * r^2)
            (by ring_nf; ring_nf at hdiv; exact hdiv)
          have hp_x : ¬(p ∣ x) := hxpure.2.2.1
          have hp_y : ¬(p ∣ y) := hypure.2.2.1
          have hp_z : ¬(p ∣ z) := hzpure.2.2.1
          have hp_xyz : ¬(p ∣ x * y * z) := by
            intro h
            rcases Nat.Prime.dvd_mul (by decide : Nat.Prime p) h with h1 | h1
            · rcases Nat.Prime.dvd_mul (by decide : Nat.Prime p) h1 with h2 | h2
              · exact hp_x h2
              · exact hp_y h2
            · exact hp_z h1
          exact hp_xyz (Nat.dvd_of_pow_dvd (by decide : 1 ≤ 2) hp2_xyz)

  -- Case: x and y divisible by r, z not
  · rcases r_mult_pure_or_6006 x hx.1 hx.2 hrx with hx6006 | hxpure
    · rcases r_mult_pure_or_6006 y hy.1 hy.2 hry with hy6006 | hypure
      · omega  -- x = y = 6006
      · -- x = 6006, y pure r, z not divisible by r
        -- Need r² | xyz. v_r(x) = 1, v_r(y) = 1, v_r(z) = 0. Total = 2. OK so far.
        -- Need p² | xyz. v_p(x) = 1, v_p(y) = 0, v_p(z) = ?
        -- Need q² | xyz. v_q(x) = 1, v_q(y) = 0, v_q(z) = ?
        -- So z must have p | z and q | z. By only_6006_multi, z = 6006.
        -- But x = 6006 and x < z, contradiction.
        have hpq_z : p ∣ z ∧ q ∣ z := by
          constructor
          · -- Need p | z
            have hp2_xyz : p^2 ∣ x * y * z := Nat.dvd_of_mul_dvd_mul_right (by decide : 0 < q^2 * r^2)
              (by ring_nf; ring_nf at hdiv; exact hdiv)
            have hp_x : p ∣ x := by simp [hx6006, p]; decide
            have hp2_x : ¬(p^2 ∣ x) := by simp [hx6006, p]; decide
            have hp_y : ¬(p ∣ y) := hypure.2.2.1
            -- p² | xyz, p|x, p²∤x, p∤y → p|z
            have hp_yz : p ∣ y * z := by
              sorry
            rcases Nat.Prime.dvd_mul (by decide : Nat.Prime p) hp_yz with h | h
            · exact absurd h hp_y
            · exact h
          · -- Need q | z (similar)
            have hq2_xyz : q^2 ∣ x * y * z := Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < p^2)
              (Nat.dvd_of_mul_dvd_mul_right (by decide : 0 < r^2) (by ring_nf; ring_nf at hdiv; exact hdiv))
            have hq_x : q ∣ x := by simp [hx6006, q]; decide
            have hq2_x : ¬(q^2 ∣ x) := by simp [hx6006, q]; decide
            have hq_y : ¬(q ∣ y) := hypure.2.2.2
            have hq_yz : q ∣ y * z := by
              sorry
            rcases Nat.Prime.dvd_mul (by decide : Nat.Prime q) hq_yz with h | h
            · exact absurd h hq_y
            · exact h
        have hz6006 := only_6006_multi z hz.1 hz.2 (Or.inl hpq_z)
        omega  -- x = z = 6006 contradicts x < z
    · -- x pure r
      rcases r_mult_pure_or_6006 y hy.1 hy.2 hry with hy6006 | hypure
      · -- y = 6006, x pure r, z not divisible by r
        -- Similar: z must have p | z and q | z, so z = 6006, but y < z
        have hpq_z : p ∣ z ∧ q ∣ z := by
          constructor
          · have hp2_xyz : p^2 ∣ x * y * z := Nat.dvd_of_mul_dvd_mul_right (by decide : 0 < q^2 * r^2)
              (by ring_nf; ring_nf at hdiv; exact hdiv)
            have hp_x : ¬(p ∣ x) := hxpure.2.2.1
            have hp_y : p ∣ y := by simp [hy6006, p]; decide
            have hp2_y : ¬(p^2 ∣ y) := by simp [hy6006, p]; decide
            have hp_xz : p ∣ x * z := by sorry
            rcases Nat.Prime.dvd_mul (by decide : Nat.Prime p) hp_xz with h | h
            · exact absurd h hp_x
            · exact h
          · have hq2_xyz : q^2 ∣ x * y * z := Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < p^2)
              (Nat.dvd_of_mul_dvd_mul_right (by decide : 0 < r^2) (by ring_nf; ring_nf at hdiv; exact hdiv))
            have hq_x : ¬(q ∣ x) := hxpure.2.2.2
            have hq_y : q ∣ y := by simp [hy6006, q]; decide
            have hq2_y : ¬(q^2 ∣ y) := by simp [hy6006, q]; decide
            have hq_xz : q ∣ x * z := by sorry
            rcases Nat.Prime.dvd_mul (by decide : Nat.Prime q) hq_xz with h | h
            · exact absurd h hq_x
            · exact h
        have hz6006 := only_6006_multi z hz.1 hz.2 (Or.inl hpq_z)
        omega
      · -- Both x and y are pure r, z not divisible by r
        -- Neither x nor y divisible by p, and z not divisible by r
        -- For r² | xyz, need v_r(xyz) ≥ 2. v_r(x) = 1, v_r(y) = 1, v_r(z) = 0. OK.
        -- For p² | xyz, neither x nor y has p. So need p² | z.
        -- For q² | xyz, neither x nor y has q. So need q² | z.
        -- So need p² | z and q² | z, i.e., (pq)² | z. But (pq)² = 5929 and 5929 < windowStart.
        have hp2_xyz : p^2 ∣ x * y * z := Nat.dvd_of_mul_dvd_mul_right (by decide : 0 < q^2 * r^2)
          (by ring_nf; ring_nf at hdiv; exact hdiv)
        have hp_x : ¬(p ∣ x) := hxpure.2.2.1
        have hp_y : ¬(p ∣ y) := hypure.2.2.1
        have hp_xyz : p ∣ x * y * z := Nat.dvd_of_pow_dvd (by decide : 1 ≤ 2) hp2_xyz
        rcases Nat.Prime.dvd_mul (by decide : Nat.Prime p) hp_xyz with h1 | h1
        · rcases Nat.Prime.dvd_mul (by decide : Nat.Prime p) h1 with h2 | h2
          · exact hp_x h2
          · exact hp_y h2
        · -- p | z. Similarly q | z. So z = 6006 by only_6006_multi. But then r | z, contradiction.
          have hq2_xyz : q^2 ∣ x * y * z := Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < p^2)
            (Nat.dvd_of_mul_dvd_mul_right (by decide : 0 < r^2) (by ring_nf; ring_nf at hdiv; exact hdiv))
          have hq_x : ¬(q ∣ x) := hxpure.2.2.2
          have hq_y : ¬(q ∣ y) := hypure.2.2.2
          have hq_xyz : q ∣ x * y * z := Nat.dvd_of_pow_dvd (by decide : 1 ≤ 2) hq2_xyz
          rcases Nat.Prime.dvd_mul (by decide : Nat.Prime q) hq_xyz with h2 | h2
          · rcases Nat.Prime.dvd_mul (by decide : Nat.Prime q) h2 with h3 | h3
            · exact hq_x h3
            · exact hq_y h3
          · -- q | z and p | z
            have hz6006 := only_6006_multi z hz.1 hz.2 (Or.inl ⟨h1, h2⟩)
            -- But z = 6006 means r | z, contradicting hrz
            have hr_z : r ∣ z := by simp [hz6006, r]; decide
            exact hrz hr_z

  -- Case: x and z divisible by r, y not
  · rcases r_mult_pure_or_6006 x hx.1 hx.2 hrx with hx6006 | hxpure
    · rcases r_mult_pure_or_6006 z hz.1 hz.2 hrz with hz6006 | hzpure
      · omega  -- x = z = 6006
      · -- x = 6006, z pure r, y not divisible by r
        -- y must have p | y and q | y, so y = 6006, but x < y
        have hpq_y : p ∣ y ∧ q ∣ y := by
          constructor
          · have hp2_xyz : p^2 ∣ x * y * z := Nat.dvd_of_mul_dvd_mul_right (by decide : 0 < q^2 * r^2)
              (by ring_nf; ring_nf at hdiv; exact hdiv)
            have hp_x : p ∣ x := by simp [hx6006, p]; decide
            have hp2_x : ¬(p^2 ∣ x) := by simp [hx6006, p]; decide
            have hp_z : ¬(p ∣ z) := hzpure.2.2.1
            have hp_yz : p ∣ y * z := by sorry
            rcases Nat.Prime.dvd_mul (by decide : Nat.Prime p) hp_yz with h | h
            · exact h
            · exact absurd h hp_z
          · have hq2_xyz : q^2 ∣ x * y * z := Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < p^2)
              (Nat.dvd_of_mul_dvd_mul_right (by decide : 0 < r^2) (by ring_nf; ring_nf at hdiv; exact hdiv))
            have hq_x : q ∣ x := by simp [hx6006, q]; decide
            have hq2_x : ¬(q^2 ∣ x) := by simp [hx6006, q]; decide
            have hq_z : ¬(q ∣ z) := hzpure.2.2.2
            have hq_yz : q ∣ y * z := by sorry
            rcases Nat.Prime.dvd_mul (by decide : Nat.Prime q) hq_yz with h | h
            · exact h
            · exact absurd h hq_z
        have hy6006 := only_6006_multi y hy.1 hy.2 (Or.inl hpq_y)
        omega
    · rcases r_mult_pure_or_6006 z hz.1 hz.2 hrz with hz6006 | hzpure
      · -- z = 6006, x pure r, y not divisible by r
        have hpq_y : p ∣ y ∧ q ∣ y := by
          constructor
          · have hp2_xyz : p^2 ∣ x * y * z := Nat.dvd_of_mul_dvd_mul_right (by decide : 0 < q^2 * r^2)
              (by ring_nf; ring_nf at hdiv; exact hdiv)
            have hp_x : ¬(p ∣ x) := hxpure.2.2.1
            have hp_z : p ∣ z := by simp [hz6006, p]; decide
            have hp2_z : ¬(p^2 ∣ z) := by simp [hz6006, p]; decide
            have hp_xy : p ∣ x * y := by sorry
            rcases Nat.Prime.dvd_mul (by decide : Nat.Prime p) hp_xy with h | h
            · exact absurd h hp_x
            · exact h
          · have hq2_xyz : q^2 ∣ x * y * z := Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < p^2)
              (Nat.dvd_of_mul_dvd_mul_right (by decide : 0 < r^2) (by ring_nf; ring_nf at hdiv; exact hdiv))
            have hq_x : ¬(q ∣ x) := hxpure.2.2.2
            have hq_z : q ∣ z := by simp [hz6006, q]; decide
            have hq2_z : ¬(q^2 ∣ z) := by simp [hz6006, q]; decide
            have hq_xy : q ∣ x * y := by sorry
            rcases Nat.Prime.dvd_mul (by decide : Nat.Prime q) hq_xy with h | h
            · exact absurd h hq_x
            · exact h
        have hy6006 := only_6006_multi y hy.1 hy.2 (Or.inl hpq_y)
        omega
      · -- Both x and z are pure r, y not divisible by r
        have hp2_xyz : p^2 ∣ x * y * z := Nat.dvd_of_mul_dvd_mul_right (by decide : 0 < q^2 * r^2)
          (by ring_nf; ring_nf at hdiv; exact hdiv)
        have hp_x : ¬(p ∣ x) := hxpure.2.2.1
        have hp_z : ¬(p ∣ z) := hzpure.2.2.1
        have hp_xyz : p ∣ x * y * z := Nat.dvd_of_pow_dvd (by decide : 1 ≤ 2) hp2_xyz
        rcases Nat.Prime.dvd_mul (by decide : Nat.Prime p) hp_xyz with h1 | h1
        · rcases Nat.Prime.dvd_mul (by decide : Nat.Prime p) h1 with h2 | h2
          · exact hp_x h2
          · have hq2_xyz : q^2 ∣ x * y * z := Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < p^2)
              (Nat.dvd_of_mul_dvd_mul_right (by decide : 0 < r^2) (by ring_nf; ring_nf at hdiv; exact hdiv))
            have hq_x : ¬(q ∣ x) := hxpure.2.2.2
            have hq_z : ¬(q ∣ z) := hzpure.2.2.2
            have hq_xyz : q ∣ x * y * z := Nat.dvd_of_pow_dvd (by decide : 1 ≤ 2) hq2_xyz
            rcases Nat.Prime.dvd_mul (by decide : Nat.Prime q) hq_xyz with h3 | h3
            · rcases Nat.Prime.dvd_mul (by decide : Nat.Prime q) h3 with h4 | h4
              · exact hq_x h4
              · have hy6006 := only_6006_multi y hy.1 hy.2 (Or.inl ⟨h2, h4⟩)
                have hr_y : r ∣ y := by simp [hy6006, r]; decide
                exact hry hr_y
            · exact hq_z h3
        · exact hp_z h1

  -- Case: y and z divisible by r, x not
  · rcases r_mult_pure_or_6006 y hy.1 hy.2 hry with hy6006 | hypure
    · rcases r_mult_pure_or_6006 z hz.1 hz.2 hrz with hz6006 | hzpure
      · omega  -- y = z = 6006
      · -- y = 6006, z pure r, x not divisible by r
        have hpq_x : p ∣ x ∧ q ∣ x := by
          constructor
          · have hp2_xyz : p^2 ∣ x * y * z := Nat.dvd_of_mul_dvd_mul_right (by decide : 0 < q^2 * r^2)
              (by ring_nf; ring_nf at hdiv; exact hdiv)
            have hp_y : p ∣ y := by simp [hy6006, p]; decide
            have hp2_y : ¬(p^2 ∣ y) := by simp [hy6006, p]; decide
            have hp_z : ¬(p ∣ z) := hzpure.2.2.1
            have hp_xz : p ∣ x * z := by sorry
            rcases Nat.Prime.dvd_mul (by decide : Nat.Prime p) hp_xz with h | h
            · exact h
            · exact absurd h hp_z
          · have hq2_xyz : q^2 ∣ x * y * z := Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < p^2)
              (Nat.dvd_of_mul_dvd_mul_right (by decide : 0 < r^2) (by ring_nf; ring_nf at hdiv; exact hdiv))
            have hq_y : q ∣ y := by simp [hy6006, q]; decide
            have hq2_y : ¬(q^2 ∣ y) := by simp [hy6006, q]; decide
            have hq_z : ¬(q ∣ z) := hzpure.2.2.2
            have hq_xz : q ∣ x * z := by sorry
            rcases Nat.Prime.dvd_mul (by decide : Nat.Prime q) hq_xz with h | h
            · exact h
            · exact absurd h hq_z
        have hx6006 := only_6006_multi x hx.1 hx.2 (Or.inl hpq_x)
        omega
    · rcases r_mult_pure_or_6006 z hz.1 hz.2 hrz with hz6006 | hzpure
      · -- z = 6006, y pure r, x not divisible by r
        have hpq_x : p ∣ x ∧ q ∣ x := by
          constructor
          · have hp2_xyz : p^2 ∣ x * y * z := Nat.dvd_of_mul_dvd_mul_right (by decide : 0 < q^2 * r^2)
              (by ring_nf; ring_nf at hdiv; exact hdiv)
            have hp_y : ¬(p ∣ y) := hypure.2.2.1
            have hp_z : p ∣ z := by simp [hz6006, p]; decide
            have hp2_z : ¬(p^2 ∣ z) := by simp [hz6006, p]; decide
            have hp_xy : p ∣ x * y := by sorry
            rcases Nat.Prime.dvd_mul (by decide : Nat.Prime p) hp_xy with h | h
            · exact h
            · exact absurd h hp_y
          · have hq2_xyz : q^2 ∣ x * y * z := Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < p^2)
              (Nat.dvd_of_mul_dvd_mul_right (by decide : 0 < r^2) (by ring_nf; ring_nf at hdiv; exact hdiv))
            have hq_y : ¬(q ∣ y) := hypure.2.2.2
            have hq_z : q ∣ z := by simp [hz6006, q]; decide
            have hq2_z : ¬(q^2 ∣ z) := by simp [hz6006, q]; decide
            have hq_xy : q ∣ x * y := by sorry
            rcases Nat.Prime.dvd_mul (by decide : Nat.Prime q) hq_xy with h | h
            · exact h
            · exact absurd h hq_y
        have hx6006 := only_6006_multi x hx.1 hx.2 (Or.inl hpq_x)
        omega
      · -- Both y and z are pure r, x not divisible by r
        have hp2_xyz : p^2 ∣ x * y * z := Nat.dvd_of_mul_dvd_mul_right (by decide : 0 < q^2 * r^2)
          (by ring_nf; ring_nf at hdiv; exact hdiv)
        have hp_y : ¬(p ∣ y) := hypure.2.2.1
        have hp_z : ¬(p ∣ z) := hzpure.2.2.1
        have hp_xyz : p ∣ x * y * z := Nat.dvd_of_pow_dvd (by decide : 1 ≤ 2) hp2_xyz
        rcases Nat.Prime.dvd_mul (by decide : Nat.Prime p) hp_xyz with h1 | h1
        · rcases Nat.Prime.dvd_mul (by decide : Nat.Prime p) h1 with h2 | h2
          · have hq2_xyz : q^2 ∣ x * y * z := Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < p^2)
              (Nat.dvd_of_mul_dvd_mul_right (by decide : 0 < r^2) (by ring_nf; ring_nf at hdiv; exact hdiv))
            have hq_y : ¬(q ∣ y) := hypure.2.2.2
            have hq_z : ¬(q ∣ z) := hzpure.2.2.2
            have hq_xyz : q ∣ x * y * z := Nat.dvd_of_pow_dvd (by decide : 1 ≤ 2) hq2_xyz
            rcases Nat.Prime.dvd_mul (by decide : Nat.Prime q) hq_xyz with h3 | h3
            · rcases Nat.Prime.dvd_mul (by decide : Nat.Prime q) h3 with h4 | h4
              · have hx6006 := only_6006_multi x hx.1 hx.2 (Or.inl ⟨h2, h4⟩)
                have hr_x : r ∣ x := by simp [hx6006, r]; decide
                exact hrx hr_x
              · exact hq_y h4
            · exact hq_z h3
          · exact hp_y h2
        · exact hp_z h1

  -- Case: only x divisible by r
  · -- Need r² | xyz but only r | x. Impossible without r² | x.
    have hr2_xyz : r^2 ∣ x * y * z := Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < p^2 * q^2)
      (by ring_nf; ring_nf at hdiv; exact hdiv)
    have hr_xyz : r ∣ x * y * z := Nat.dvd_of_pow_dvd (by decide : 1 ≤ 2) hr2_xyz
    -- r | xyz and r | x, but r ∤ y and r ∤ z
    -- So v_r(xyz) = v_r(x). Need v_r(x) ≥ 2, i.e., r² | x.
    have hr2_x : r^2 ∣ x := by
      have : r ∣ y * z → False := by
        intro h
        rcases Nat.Prime.dvd_mul (by decide : Nat.Prime r) h with h1 | h1
        · exact hry h1
        · exact hrz h1
      -- r² | xyz, r | x, r ∤ yz → r² | x
      sorry
    exact hx_no_r2 hr2_x

  -- Case: only y divisible by r
  · have hr2_xyz : r^2 ∣ x * y * z := Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < p^2 * q^2)
      (by ring_nf; ring_nf at hdiv; exact hdiv)
    have hr2_y : r^2 ∣ y := by
      sorry
    exact hy_no_r2 hr2_y

  -- Case: only z divisible by r
  · have hr2_xyz : r^2 ∣ x * y * z := Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < p^2 * q^2)
      (by ring_nf; ring_nf at hdiv; exact hdiv)
    have hr2_z : r^2 ∣ z := by
      sorry
    exact hz_no_r2 hr2_z

  -- Case: none divisible by r
  · have hr2_xyz : r^2 ∣ x * y * z := Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < p^2 * q^2)
      (by ring_nf; ring_nf at hdiv; exact hdiv)
    have hr_xyz : r ∣ x * y * z := Nat.dvd_of_pow_dvd (by decide : 1 ≤ 2) hr2_xyz
    rcases Nat.Prime.dvd_mul (by decide : Nat.Prime r) hr_xyz with h1 | h1
    · rcases Nat.Prime.dvd_mul (by decide : Nat.Prime r) h1 with h2 | h2
      · exact hrx h2
      · exact hry h2
    · exact hrz h1
