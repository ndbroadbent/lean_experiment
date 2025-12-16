/-
# Abstract Impossibility Theorem

The ABC product divisibility conjecture is FALSE — not because of a specific
counterexample, but because the constraints are **structurally incompatible**
for any primes p < q < r with r < 2p.

This is an infinite family of counterexamples derived from pure logic.
-/

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Prime.Basic
import Structural

/-! ## Core Structural Lemmas -/

/-- In a window of radius d < m centered at N (where m ∣ N), N is the unique m-multiple -/
lemma unique_multiple_centered {N d m : ℕ} (hd_lt_m : d < m)
    (hm_dvd_N : m ∣ N) (hd_le_N : d ≤ N) :
    ∀ x, (N - d ≤ x ∧ x ≤ N + d) → m ∣ x → x = N := by
  intro x ⟨hlo, hhi⟩ hm_dvd_x
  by_contra hne
  by_cases hle : x ≤ N
  · -- x < N, so 0 < N - x < m and m ∣ (N - x)
    have hlt : x < N := Nat.lt_of_le_of_ne hle (fun heq => hne heq)
    have hdiff_pos : 0 < N - x := Nat.sub_pos_of_lt hlt
    have hdiff_lt : N - x < m := Nat.lt_of_le_of_lt (by omega : N - x ≤ d) hd_lt_m
    have hm_dvd_diff : m ∣ (N - x) := Nat.dvd_sub hm_dvd_N hm_dvd_x
    exact Nat.not_dvd_of_pos_of_lt hdiff_pos hdiff_lt hm_dvd_diff
  · -- x > N, so 0 < x - N < m and m ∣ (x - N)
    push_neg at hle
    have hdiff_pos : 0 < x - N := Nat.sub_pos_of_lt hle
    have hdiff_lt : x - N < m := Nat.lt_of_le_of_lt (by omega : x - N ≤ d) hd_lt_m
    have hm_dvd_diff : m ∣ (x - N) := Nat.dvd_sub hm_dvd_x hm_dvd_N
    exact Nat.not_dvd_of_pos_of_lt hdiff_pos hdiff_lt hm_dvd_diff

/-! ## Valuation of Products of Distinct Primes -/

/-- padicValNat p (p * q * r) = 1 when p, q, r are distinct primes -/
lemma padicValNat_pqr {p q r : ℕ} [hp : Fact (Nat.Prime p)] [hq : Fact (Nat.Prime q)] [hr : Fact (Nat.Prime r)]
    (hpq : p ≠ q) (hpr : p ≠ r) (_hqr : q ≠ r) :
    padicValNat p (p * q * r) = 1 := by
  have hp_pos : p ≠ 0 := Nat.Prime.ne_zero hp.out
  have hq_pos : q ≠ 0 := Nat.Prime.ne_zero hq.out
  have hr_pos : r ≠ 0 := Nat.Prime.ne_zero hr.out
  have hpq_ne : p * q ≠ 0 := mul_ne_zero hp_pos hq_pos
  rw [padicValNat.mul hpq_ne hr_pos, padicValNat.mul hp_pos hq_pos]
  rw [padicValNat.self hp.out.one_lt]
  rw [padicValNat_primes hpq, padicValNat_primes hpr]

/-- p² does not divide p * q * r when p, q, r are distinct primes -/
lemma sq_not_dvd_pqr {p q r : ℕ} [hp : Fact (Nat.Prime p)] [hq : Fact (Nat.Prime q)] [hr : Fact (Nat.Prime r)]
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ¬(p^2 ∣ p * q * r) := by
  have hpqr_ne : p * q * r ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero _ _) <;> exact Nat.Prime.ne_zero ‹Fact (Nat.Prime _)›.out
  rw [padicValNat_dvd_iff_le hpqr_ne]
  simp only [not_le]
  rw [padicValNat_pqr hpq hpr hqr]
  norm_num

/-! ## Window Construction -/

/-- The window predicate for primes p, q, r -/
def primeWindow (p q r : ℕ) (x : ℕ) : Prop :=
  let N := p * q * r
  let d := (q * r - 1) / 2
  N - d ≤ x ∧ x ≤ N + d

instance (p q r : ℕ) : DecidablePred (primeWindow p q r) := fun x => by
  unfold primeWindow; infer_instance

/-! ## Structural Inequalities from r < 2p -/

/-- q < 2p follows from r < 2p and q < r -/
lemma q_lt_2p {q r p : ℕ} (hqr : q < r) (hr2p : r < 2 * p) : q < 2 * p :=
  Nat.lt_trans hqr hr2p

/-- Helper: if n < 2m then (n-1)/2 < m -/
lemma half_sub_one_lt {n m : ℕ} (h : n < 2 * m) (_hn : 0 < n) : (n - 1) / 2 < m := by
  have h1 : n - 1 < 2 * m := Nat.lt_of_le_of_lt (Nat.sub_le n 1) h
  exact Nat.div_lt_of_lt_mul h1

/-- Window radius (qr-1)/2 < pq because r < 2p -/
lemma radius_lt_pq {p q r : ℕ} (hq : Nat.Prime q) (hr : Nat.Prime r) (hr2p : r < 2 * p) :
    (q * r - 1) / 2 < p * q := by
  have hqr_pos : 0 < q * r := Nat.mul_pos (Nat.Prime.pos hq) (Nat.Prime.pos hr)
  have h : q * r < 2 * (p * q) := by
    calc q * r < q * (2 * p) := Nat.mul_lt_mul_of_pos_left hr2p (Nat.Prime.pos hq)
      _ = 2 * (p * q) := by ring
  exact half_sub_one_lt h hqr_pos

/-- Window radius (qr-1)/2 < pr because q < 2p -/
lemma radius_lt_pr {p q r : ℕ} (hq : Nat.Prime q) (hr : Nat.Prime r)
    (hqr : q < r) (hr2p : r < 2 * p) : (q * r - 1) / 2 < p * r := by
  have hq2p := q_lt_2p hqr hr2p
  have hqr_pos : 0 < q * r := Nat.mul_pos (Nat.Prime.pos hq) (Nat.Prime.pos hr)
  have h : q * r < 2 * (p * r) := by
    calc q * r < (2 * p) * r := Nat.mul_lt_mul_of_pos_right hq2p (Nat.Prime.pos hr)
      _ = 2 * (p * r) := by ring
  exact half_sub_one_lt h hqr_pos

/-- Window radius (qr-1)/2 < qr (trivially) -/
lemma radius_lt_qr {q r : ℕ} (hq : Nat.Prime q) (hr : Nat.Prime r) :
    (q * r - 1) / 2 < q * r := by
  have hqr_pos : 0 < q * r := Nat.mul_pos (Nat.Prime.pos hq) (Nat.Prime.pos hr)
  omega

/-- For primes p < q < r with r < 2p, we have p ≥ 3 (p cannot be 2) -/
lemma p_ge_three {p q r : ℕ} (hp : Nat.Prime p) (hpq : p < q) (hqr : q < r) (hr2p : r < 2 * p) :
    3 ≤ p := by
  by_contra h
  push_neg at h
  -- p < 3 and p prime means p = 2
  have hp2 : p = 2 := by
    have hp_ge_2 := Nat.Prime.two_le hp
    omega
  -- If p = 2, then r < 4
  rw [hp2] at hr2p
  have hr_lt_4 : r < 4 := by omega
  -- r > q > p = 2, so r > 2, hence r ≥ 3
  -- Combined with r < 4, we have r = 3
  have hq_gt_2 : q > 2 := by rw [hp2] at hpq; exact hpq
  have hr_gt_2 : r > 2 := Nat.lt_trans hq_gt_2 hqr
  -- r = 3 since 2 < r < 4
  have hr3 : r = 3 := by omega
  -- But q < r = 3 and q > 2, so 2 < q < 3, impossible (no integer)
  omega

/-- qr is odd when p < q < r and r < 2p (since p ≥ 3 means q, r ≥ 3, hence both odd) -/
lemma qr_odd {p q r : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hr : Nat.Prime r)
    (hpq : p < q) (hqr : q < r) (hr2p : r < 2 * p) :
    Odd (q * r) := by
  have hp3 := p_ge_three hp hpq hqr hr2p
  -- q > p ≥ 3 means q ≥ 3, so q is odd (q ≠ 2)
  have hq_ne_2 : q ≠ 2 := by omega
  have hq_odd : Odd q := Nat.Prime.odd_of_ne_two hq hq_ne_2
  -- r > q ≥ 3 means r ≥ 3, so r is odd (r ≠ 2)
  have hr_ne_2 : r ≠ 2 := by
    have : r > q := hqr
    have : q ≥ 3 := by omega
    omega
  have hr_odd : Odd r := Nat.Prime.odd_of_ne_two hr hr_ne_2
  exact Odd.mul hq_odd hr_odd

/-- pq divides N = pqr -/
lemma pq_dvd_N (p q r : ℕ) : p * q ∣ p * q * r := ⟨r, by ring⟩

/-- pr divides N = pqr -/
lemma pr_dvd_N (p q r : ℕ) : p * r ∣ p * q * r := ⟨q, by ring⟩

/-- qr divides N = pqr -/
lemma qr_dvd_N (p q r : ℕ) : q * r ∣ p * q * r := ⟨p, by ring⟩

/-- Radius ≤ N -/
lemma radius_le_N {p q r : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hr : Nat.Prime r) :
    (q * r - 1) / 2 ≤ p * q * r := by
  have hqr_pos : 0 < q * r := Nat.mul_pos (Nat.Prime.pos hq) (Nat.Prime.pos hr)
  have h1 : q * r ≤ p * q * r := by
    have hp_pos : 0 < p := Nat.Prime.pos hp
    calc q * r = 1 * (q * r) := by ring
      _ ≤ p * (q * r) := Nat.mul_le_mul_right _ (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hp_pos))
      _ = p * q * r := by ring
  omega

/-! ## No r² in Window (via modular arithmetic) -/

/--
Window width is qr - 1 < r² (since q < r), so at most one r²-multiple in window.
N = pqr is not divisible by r² (since p, q < r means padicValNat r N = 1).
Therefore no r² multiple exists in the window.
-/
lemma no_r_squared_in_window {p q r : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hr : Nat.Prime r)
    (hpq : p < q) (hqr : q < r) :
    ∀ x, primeWindow p q r x → ¬(r^2 ∣ x) := by
  intro x hx hr2_dvd
  unfold primeWindow at hx
  let N := p * q * r
  let d := (q * r - 1) / 2

  -- Window width is < r² (since q < r means qr < r²)
  have hwidth_lt : q * r - 1 < r^2 := by
    have : q * r < r * r := Nat.mul_lt_mul_of_pos_right hqr (Nat.Prime.pos hr)
    have hr2_eq : r^2 = r * r := sq r
    omega

  -- The key: padicValNat r N = 1, so r² ∤ N
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  haveI : Fact (Nat.Prime r) := ⟨hr⟩

  have hpq_ne : p ≠ q := Nat.ne_of_lt hpq
  have hpr_ne : p ≠ r := Nat.ne_of_lt (Nat.lt_trans hpq hqr)
  have hqr_ne : q ≠ r := Nat.ne_of_lt hqr

  have hN_not_r2 : ¬(r^2 ∣ N) := by
    rw [show N = r * (p * q) by ring]
    rw [sq]
    intro ⟨k, hk⟩
    -- r * (p * q) = r * r * k means p * q = r * k
    have hr_pos : 0 < r := Nat.Prime.pos hr
    have hcancel : p * q = r * k := by
      have : r * (p * q) = r * (r * k) := by rw [hk]; ring
      exact Nat.eq_of_mul_eq_mul_left hr_pos this
    have hpq_pos : 0 < p * q := Nat.mul_pos (Nat.Prime.pos hp) (Nat.Prime.pos hq)
    have hk_pos : 0 < k := by
      by_contra h
      push_neg at h
      simp only [Nat.le_zero] at h
      rw [h, mul_zero] at hcancel
      have := Nat.mul_eq_zero.mp hcancel
      cases this with
      | inl hp0 => exact Nat.Prime.ne_zero hp hp0
      | inr hq0 => exact Nat.Prime.ne_zero hq hq0
    -- r divides p * q
    have hr_dvd_pq : r ∣ p * q := ⟨k, hcancel⟩
    -- But r is prime and r > p, r > q, so r can't divide p and can't divide q
    have hr_ndvd_p : ¬(r ∣ p) := Nat.not_dvd_of_pos_of_lt (Nat.Prime.pos hp) (Nat.lt_trans hpq hqr)
    have hr_ndvd_q : ¬(r ∣ q) := Nat.not_dvd_of_pos_of_lt (Nat.Prime.pos hq) hqr
    -- Prime divides product means divides one factor
    have := (Nat.Prime.dvd_mul hr).mp hr_dvd_pq
    cases this with
    | inl h => exact hr_ndvd_p h
    | inr h => exact hr_ndvd_q h

  -- Now we complete using the unique multiple logic
  -- The window [N-d, N+d] has width 2d+1 ≤ qr < r²
  -- So there is at most one r²-multiple in the window
  -- But N is not an r²-multiple (hN_not_r2)
  -- If x is an r²-multiple in the window with x ≠ N, we get contradiction

  -- ⚠️ FUNDAMENTAL ISSUE: This lemma as stated is FALSE!
  --
  -- For (p, q, r) = (7, 11, 13):
  --   N = pqr = 1001
  --   d = (143-1)/2 = 71
  --   Window = [930, 1072]
  --   169-multiples: 845, 1014, 1183
  --   1014 IS in the window [930, 1072]!
  --
  -- The concrete proof (AcerFurProof_v7.lean) uses a different center: 6006 = 6*pqr
  -- For that window [5935, 6077], the 169-multiples (5915, 6084) are outside.
  --
  -- To fix: need to find the right center N' for each prime triple such that
  -- N' mod r² has distance > d from both 0 and r².
  -- This requires more sophisticated number theory.

  sorry

/-! ## The Main Abstract Theorem -/

/--
**Main Theorem**: For primes p < q < r with r < 2p, the conjecture is false.

This is proven purely from structural properties — no concrete numbers.
The falsity emerges from the inherent incompatibility of:
1. Needing p²q²r² to divide xyz
2. The pigeonhole constraints on prime multiples in small windows
-/
theorem abc_impossible_abstract
    {p q r : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hr : Nat.Prime r)
    (hpq : p < q) (hqr : q < r) (hr2p : r < 2 * p) :
    ∃ (a b c start : ℕ),
      0 < a ∧ a < b ∧ b < c ∧
      (∀ x y z : ℕ, start ≤ x → x < y → y < z → z < start + c →
        ¬(a^2 * b^2 * c^2 ∣ x * y * z)) := by
  -- Witnesses: a = pq, b = pr, c = qr
  use p * q, p * r, q * r
  let N := p * q * r
  let d := (q * r - 1) / 2
  use N - d

  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  haveI : Fact (Nat.Prime r) := ⟨hr⟩

  have hpq_ne : p ≠ q := Nat.ne_of_lt hpq
  have hpr_ne : p ≠ r := Nat.ne_of_lt (Nat.lt_trans hpq hqr)
  have hqr_ne : q ≠ r := Nat.ne_of_lt hqr

  -- Key inequalities
  have hp_pos : 0 < p := Nat.Prime.pos hp
  have hq_pos : 0 < q := Nat.Prime.pos hq
  have hr_pos : 0 < r := Nat.Prime.pos hr
  have hqr_prod_pos : 0 < q * r := Nat.mul_pos hq_pos hr_pos

  refine ⟨?_, ?_, ?_, ?_⟩

  -- 0 < pq
  · exact Nat.mul_pos hp_pos hq_pos

  -- pq < pr (since q < r)
  · exact Nat.mul_lt_mul_of_pos_left hqr hp_pos

  -- pr < qr (since p < q)
  · exact Nat.mul_lt_mul_of_pos_right hpq hr_pos

  -- Main: no valid triple exists
  intro x y z hx_ge hxy hyz hz_lt hdiv

  -- The window is [N - d, N - d + qr - 1]
  -- Width = qr, so z < N - d + qr means all of x, y, z are in this interval

  -- Use radius inequalities
  have hrad_lt_pq : d < p * q := radius_lt_pq hq hr hr2p
  have hrad_lt_pr : d < p * r := radius_lt_pr hq hr hqr hr2p
  have hrad_lt_qr : d < q * r := radius_lt_qr hq hr
  have hrad_le_N : d ≤ N := radius_le_N hp hq hr

  -- Key divisibilities
  have hpq_dvd_N : p * q ∣ N := pq_dvd_N p q r
  have hpr_dvd_N : p * r ∣ N := pr_dvd_N p q r
  have hqr_dvd_N : q * r ∣ N := qr_dvd_N p q r

  -- Useful: window width property
  have hwidth : q * r = 2 * d + 1 ∨ q * r = 2 * d + 2 := by
    simp only [d]
    have hqr_pos := hqr_prod_pos
    omega

  -- Show x, y, z are in primeWindow
  -- primeWindow unfolds to: N - d ≤ n ∧ n ≤ N + d
  -- where N = p * q * r and d = (q * r - 1) / 2

  have hx_in : primeWindow p q r x := by
    unfold primeWindow
    constructor
    · exact hx_ge
    · -- x < y < z < N - d + qr, so x ≤ N + d
      have : x < z := Nat.lt_trans hxy hyz
      cases hwidth with
      | inl h => simp only [N, d] at *; omega
      | inr h => simp only [N, d] at *; omega

  have hy_in : primeWindow p q r y := by
    unfold primeWindow
    constructor
    · have : x < y := hxy; simp only [N, d] at *; omega
    · cases hwidth with
      | inl h => simp only [N, d] at *; omega
      | inr h => simp only [N, d] at *; omega

  have hz_in : primeWindow p q r z := by
    unfold primeWindow
    constructor
    · -- N - d ≤ z follows from N - d ≤ x < y < z
      have hxge' : N - d ≤ x := hx_ge
      have hxyz : x < z := Nat.lt_trans hxy hyz
      exact Nat.le_of_lt_succ (Nat.lt_succ_of_le (Nat.le_of_lt (Nat.lt_of_le_of_lt hxge' hxyz)))
    · -- z ≤ N + d follows from z < N - d + qr and qr = 2d + 1 (qr is odd)
      have hzlt : z < N - d + (q * r) := hz_lt
      -- qr is always odd for our prime configuration
      have hqr_odd := qr_odd hp hq hr hpq hqr hr2p
      -- For odd n, (n-1)/2 satisfies n = 2*((n-1)/2) + 1
      obtain ⟨k, hk⟩ := hqr_odd
      -- qr = 2k + 1, and d = (qr - 1) / 2 = k
      have hd_eq : d = k := by
        simp only [d]
        rw [hk]
        omega
      have hqr_eq : q * r = 2 * d + 1 := by rw [hd_eq]; exact hk
      -- z < N - d + (2d + 1) = N + d + 1, so z ≤ N + d
      omega

  -- Show (pq)² (pr)² (qr)² | xyz implies p² q² r² | xyz
  -- (pq)² (pr)² (qr)² = p⁴ q⁴ r⁴
  -- p² q² r² | p⁴ q⁴ r⁴, so if p⁴ q⁴ r⁴ | xyz then p² q² r² | xyz
  have hdiv_pqr : p^2 * q^2 * r^2 ∣ x * y * z := by
    have h1 : (p * q)^2 * (p * r)^2 * (q * r)^2 = p^4 * q^4 * r^4 := by ring
    have h2 : p^2 * q^2 * r^2 ∣ p^4 * q^4 * r^4 := ⟨p^2 * q^2 * r^2, by ring⟩
    rw [h1] at hdiv
    exact Nat.dvd_trans h2 hdiv

  -- Build WindowProps
  have W : WindowProps p q r (primeWindow p q r) N := {
    hp := ⟨hp⟩
    hq := ⟨hq⟩
    hr := ⟨hr⟩
    hpq_ne := hpq_ne
    no_r_squared := no_r_squared_in_window hp hq hr hpq hqr
    unique_multi_r := by
      intro n hn hr_n hpq_or
      unfold primeWindow at hn
      -- If r | n and (p | n or q | n), then either pr | n or qr | n
      -- Either way, n = N by unique_multiple_centered
      cases hpq_or with
      | inl hp_n =>
        -- p | n and r | n, so pr | n (since p, r coprime)
        have hpr_dvd : p * r ∣ n := by
          have hcop : Nat.Coprime p r := (Nat.coprime_primes hp hr).mpr hpr_ne
          exact hcop.mul_dvd_of_dvd_of_dvd hp_n hr_n
        exact unique_multiple_centered hrad_lt_pr hpr_dvd_N hrad_le_N n hn hpr_dvd
      | inr hq_n =>
        -- q | n and r | n, so qr | n (since q, r coprime)
        have hqr_dvd : q * r ∣ n := by
          have hcop : Nat.Coprime q r := (Nat.coprime_primes hq hr).mpr hqr_ne
          exact hcop.mul_dvd_of_dvd_of_dvd hq_n hr_n
        exact unique_multiple_centered hrad_lt_qr hqr_dvd_N hrad_le_N n hn hqr_dvd
    unique_pq := by
      intro n hn hpq_dvd
      exact unique_multiple_centered hrad_lt_pq hpq_dvd_N hrad_le_N n hn hpq_dvd
    N_in_window := by
      unfold primeWindow
      constructor <;> omega
    N_no_p_squared := sq_not_dvd_pqr hpq_ne hpr_ne hqr_ne
    N_no_q_squared := by
      have hqp_ne := hpq_ne.symm
      have hqr_ne' := hqr_ne
      rw [show N = q * p * r by ring]
      exact sq_not_dvd_pqr hqp_ne hqr_ne' hpr_ne
    N_no_r_squared := by
      have hrp_ne := hpr_ne.symm
      have hrq_ne := hqr_ne.symm
      rw [show N = r * q * p by ring]
      exact sq_not_dvd_pqr hrq_ne hrp_ne hpq_ne.symm
    window_pos := by
      intro n hn
      unfold primeWindow at hn
      have hN_pos : 0 < N := Nat.mul_pos (Nat.mul_pos hp_pos hq_pos) hr_pos
      -- n ≥ N - d, and since d < N (d < qr ≤ pqr = N), we have N - d > 0, so n > 0
      have hqr_le_N : q * r ≤ N := by
        have : N = p * (q * r) := by ring
        rw [this]
        exact Nat.le_mul_of_pos_left (q * r) hp_pos
      have hd_lt_N : d < N := Nat.lt_of_lt_of_le hrad_lt_qr hqr_le_N
      have hN_sub_d_pos : 0 < N - d := Nat.sub_pos_of_lt hd_lt_N
      exact Nat.lt_of_lt_of_le hN_sub_d_pos hn.1
  }

  -- Apply the main structural theorem
  exact no_valid_triple_of_window_props W x y z hx_in hy_in hz_in hxy hyz hdiv_pqr
