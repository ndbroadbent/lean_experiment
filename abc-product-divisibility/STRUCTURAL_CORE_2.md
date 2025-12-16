Got it - I’ve updated the background process accordingly.


Yes. The way to get what you want is to stop thinking “prove these window facts by computation,” and instead build a small toolkit of **symbolic lemmas** that let you prove the same window facts from:

* “this window is centered at `N`”
* “the radius is `< m`”
* “`m ∣ N`”
* “primes are coprime”
* “a congruence mod `r^2` keeps you away from multiples of `r^2`”

That lets you write the whole counterexample proof with **no `native_decide` / `decide` / `omega`**, and also without huge case analysis.

Below is a practical roadmap for “digging around Mathlib” and the exact kinds of lemmas you should either find or define locally (as 5–10 line wrappers around existing Mathlib facts). These wrappers are the missing “ergonomics” you’re feeling.

---

## 1) Replace “enumerating multiples in the window” with a centered-interval lemma

You keep proving facts like:

* “the only multiple of 77 in `[5935,6077]` is 6006”
* “the only multiple of 91 in `[5935,6077]` is 6006”
* “the only multiple of 143 in `[5935,6077]` is 6006”

You do not want to prove these by listing `5929,6006,6083`.

Instead prove the general statement once:

### Lemma: unique multiple in a centered window

If `m ∣ N` and `d < m`, then **any** `x` with `|x - N| ≤ d` and `m ∣ x` must equal `N`.

The proof is purely symbolic:

* from `m ∣ x` and `m ∣ N`, get `m ∣ (x - N)`
* but also `0 ≤ |x - N| ≤ d < m`
* the only multiple of `m` with absolute value `< m` is `0`
* so `x - N = 0`

In Lean you can implement the “only multiple is 0” part using a standard `Nat` lemma:

* if `m ∣ t` and `t < m` then `t = 0` (since `t = m*k`, and if `k ≥ 1` then `m ≤ t`)

You might not find an exact lemma already named that way, but it’s short and reusable.

**Where to look:**

* `Nat.dvd_sub` / `Nat.dvd_sub` variants (careful: needs order hypotheses)
* `Nat.abs_sub` lemmas if you use `Int`/`ZMod` route
* or avoid absolute values by using a window definition `N - d ≤ x ∧ x ≤ N + d` and proving `x-N < m` and `N-x < m` in the two cases `x ≥ N` / `x ≤ N`.

Once you have this lemma, your “only_6006_div_77” becomes 3 lines:

* `m = 77`, `N = 6006`, `d = 71`
* show `d < m`
* apply the lemma

No enumeration, no `omega`.

---

## 2) Replace “no multiple of 169 in the window” with a modular-distance lemma

Your current `no_169_in_window` is doing arithmetic on the endpoints.

The structural way is:

* you are in a centered window around `N`
* you pick `N mod r^2` to be “far” from 0
* since multiples of `r^2` are exactly the residue class 0 mod `r^2`, the window cannot contain any such number

### Lemma: avoid a residue class in a centered window

Let `m > 0`. Let `d < m/2`. If `N mod m` lies in `(d, m-d)` (meaning it’s at distance > d from 0), then
`∀ x, N-d ≤ x ≤ N+d → ¬(m ∣ x)`.

In your concrete case:

* `m = r^2`
* `d = (qr - 1)/2`
* ensure `qr < r^2` so `d < m/2` is automatic
* choose `N` so `N ≡ r*((q+1)/2) (mod r^2)` which lands away from 0

**Where to look:**

* `Nat.ModEq`, `Nat.modEq_iff_dvd`
* `ZMod` is often easier for “distance from 0 mod m” reasoning, but you can also keep it in `Nat` with `Nat.mod_lt`, `Nat.modEq_iff_dvd`, etc.

Again, you might not find a single lemma that matches this exactly, but the components exist and the glue lemma is short.

---

## 3) Stop doing 3 symmetric big cases (xy, xz, yz) and use a set-based/pigeonhole lemma

Your proof currently does:

* deduce at least two of x,y,z are divisible by 13
* split into 3 cases for which pair it is
* then repeat nearly the same argument

Instead, write a lemma:

### Lemma: two-of-three must be divisible by r

Assume:

* `∀ n ∈ {x,y,z}, vr n ≤ 1`
* and `vr x + vr y + vr z ≥ 2`

Then:
`∃ u v ∈ {x,y,z}, u ≠ v ∧ (r ∣ u) ∧ (r ∣ v)`.

This is just “if three numbers each contribute at most 1, total ≥ 2 means at least two contributors.”

In Lean, this is a tiny lemma about naturals, no number theory.

Then you never do the `rcases` into 3 branches. You pick `u` and `v` and proceed uniformly.

---

## 4) Use `padicValNat` only for the “squared prime needs two hits” step

The padic bits you’re already using are good. The main “ergonomic” improvement is to avoid repeating the `mul_ne_zero` plumbing.

Two options:

### Option A: switch to the “Or” version of dvd lemma

There is a lemma of the shape:
`p^k ∣ n ↔ n = 0 ∨ k ≤ padicValNat p n`.
Then you don’t need `n ≠ 0` everywhere.

### Option B: define a local lemma `padicValNat_mul3` that hides the nonzero conditions

You can prove once:
`padicValNat p (x*y*z) = padicValNat p x + padicValNat p y + padicValNat p z`
by cases on whether x,y,z are zero, and then reuse it everywhere.

This is exactly the kind of local wrapper that makes the proof feel “human.”

---

## 5) “No decide” for primes 7/11/13 is doable, but don’t waste time on it

If your goal is “no decide at all,” you can still avoid it for prime facts:

* Mathlib often has `Nat.prime_2`, `Nat.prime_3`, `Nat.prime_5`, `Nat.prime_7`, etc.
* If not, you can prove `Nat.Prime 7` directly from the definition with a short proof.

But this is the least interesting part. The big wins are the interval/multiple lemmas above.

If you truly want *zero computation tactics*, you’ll also want to avoid `native_decide` for `padicValNat 7 6006 = 1`. Instead, prove it by:

* show `7 ∣ 6006`
* show `7^2 ∤ 6006`
* then conclude `padicValNat 7 6006 = 1` via `padicValNat.eq_one_iff_dvd_not_dvd` style lemmas (or the `dvd_iff` + monotonicity route)

That’s more lines, but it’s fully symbolic.

---

## What to do next with your repo structure (concrete)

You said you’re at:

* `Structural.lean` generic lemma
* `WindowFacts_7_11_13.lean` concrete facts
* `Instance_7_11_13.lean`

But you want to “throw many things at it” and converge to a clean proof.

Here’s how I’d restructure WITHOUT changing your 3-file idea, but enabling exploration:

### A) Add one more file: `Toolkit.lean`

This is where you put the 5–10 short glue lemmas:

* `unique_multiple_in_centered_interval`
* `no_multiple_in_centered_interval_of_mod_distance`
* `padicValNat_mul3` (or the zero-friendly variant)
* “two-of-three contributors” lemma

Then both `Structural` and `WindowFacts` become tiny.

### B) In `WindowFacts`, prove only:

* `N` is in the window
* radius `d < 77`, `d < 91`, `d < 143`, `d < 169/2` (no automation if you really want)
* the modular fact for `N mod 169` (or `N mod 13^2`)

Everything else becomes a one-line application of toolkit lemmas.

That gives you the “pure symbolic” feel you’re after, even though the witness is still concrete.
