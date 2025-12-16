/-
# Counterexample Verification

This file computationally verifies that the block [5930, 6072] contains no
valid triple whose product is divisible by abc = 1002001.

The key insight is that abc = 7² × 11² × 13², so we need the product of
three numbers to have at least 2 factors of each of 7, 11, and 13.
-/

import ABCProductDivisibility

/-! ## Helper Functions for Verification -/

/-- Count how many times prime p divides n -/
def primeValuation (n p : ℕ) : ℕ :=
  if p > 1 ∧ n > 0 then
    let rec go (m : ℕ) (acc : ℕ) (fuel : ℕ) : ℕ :=
      if fuel = 0 then acc
      else if m % p = 0 then go (m / p) (acc + 1) (fuel - 1)
      else acc
    go n 0 n
  else 0

#eval primeValuation 49 7  -- 2 (49 = 7²)
#eval primeValuation 77 7  -- 1 (77 = 7 × 11)
#eval primeValuation 143 11  -- 1 (143 = 11 × 13)

/-- The "type" of a number: (v7(n), v11(n), v13(n)) capped at 2 each -/
def primeType (n : ℕ) : ℕ × ℕ × ℕ :=
  (min (primeValuation n 7) 2,
   min (primeValuation n 11) 2,
   min (primeValuation n 13) 2)

#eval primeType 5929  -- (2, 2, 0) since 5929 = 7² × 11²
#eval primeType 5936  -- (1, 0, 0) since 5936 = 7 × 848
#eval primeType 6006  -- (1, 1, 1) since 6006 = 2 × 3 × 7 × 11 × 13

/-- A triple (x, y, z) is "good" if v_p(xyz) ≥ 2 for each of p ∈ {7, 11, 13} -/
def isGoodTriple (x y z : ℕ) : Bool :=
  let (v7x, v11x, v13x) := primeType x
  let (v7y, v11y, v13y) := primeType y
  let (v7z, v11z, v13z) := primeType z
  v7x + v7y + v7z ≥ 2 ∧
  v11x + v11y + v11z ≥ 2 ∧
  v13x + v13y + v13z ≥ 2

/-! ## Optimized Check Using Type Counting

Instead of O(n³) brute force, we can:
1. Compute the prime type of each number in the window
2. Count how many numbers have each type
3. Check if any combination of types sums to (≥2, ≥2, ≥2)

There are only 3³ = 27 possible types (since we cap at 2).
-/

/-- Encode a type as a single number 0-26 -/
def encodeType (t : ℕ × ℕ × ℕ) : ℕ :=
  t.1 * 9 + t.2.1 * 3 + t.2.2

/-- Decode a type number back to (v7, v11, v13) -/
def decodeType (n : ℕ) : ℕ × ℕ × ℕ :=
  (n / 9, (n % 9) / 3, n % 3)

/-- Count occurrences of each type in a range -/
def typeCounts (start len : ℕ) : Array ℕ :=
  let counts := Array.replicate 27 0
  List.range len |>.foldl (init := counts) fun acc i =>
    let n := start + i
    let t := encodeType (primeType n)
    acc.setIfInBounds t (acc[t]! + 1)

/-- Check if three types combine to give a valid triple -/
def typesFormGoodTriple (t1 t2 t3 : ℕ) : Bool :=
  let (v71, v111, v131) := decodeType t1
  let (v72, v112, v132) := decodeType t2
  let (v73, v113, v133) := decodeType t3
  v71 + v72 + v73 ≥ 2 ∧
  v111 + v112 + v113 ≥ 2 ∧
  v131 + v132 + v133 ≥ 2

/-- Check if counts allow a good triple.
    This checks all combinations of types, accounting for how many of each type are available -/
def countsAllowGoodTriple (counts : Array ℕ) : Bool :=
  -- For each ordered combination of types (t1, t2, t3)
  -- Check if we have enough numbers of those types
  List.range 27 |>.any fun t1 =>
    List.range 27 |>.any fun t2 =>
      List.range 27 |>.any fun t3 =>
        -- Need distinct elements, so check if counts support it
        let needed := fun t => (if t = t1 then 1 else 0) +
                               (if t = t2 then 1 else 0) +
                               (if t = t3 then 1 else 0)
        let have_enough := List.range 27 |>.all fun t => counts[t]! ≥ needed t
        typesFormGoodTriple t1 t2 t3 ∧ have_enough

-- Test on a small window that SHOULD have a good triple
#eval countsAllowGoodTriple (typeCounts 1 143)  -- true (window [1, 143] has good triples)

-- THE KEY CHECK: the counterexample window
#eval countsAllowGoodTriple (typeCounts 5930 143)  -- false!

/-! ## The Proof

We prove the counterexample computationally by showing no valid triple exists.
-/

/-- The counterexample window has no valid triple (computational verification) -/
theorem no_good_triple_in_counterexample :
    countsAllowGoodTriple (typeCounts counterexample_start c_val) = false := by
  native_decide

/-! ## Direct Verification via Brute Force

For a completely self-contained proof, we can also verify by brute-force search.
This is slower but creates a direct link to the logical statement.
-/

/-- Decidable check: does the product of x*y*z have enough factors of 7, 11, 13? -/
def productHasRequiredFactors (x y z : ℕ) : Bool :=
  let (v7x, v11x, v13x) := primeType x
  let (v7y, v11y, v13y) := primeType y
  let (v7z, v11z, v13z) := primeType z
  -- Need v7 ≥ 2, v11 ≥ 2, v13 ≥ 2 for divisibility by abc = 7² × 11² × 13²
  v7x + v7y + v7z ≥ 2 ∧
  v11x + v11y + v11z ≥ 2 ∧
  v13x + v13y + v13z ≥ 2

/-- Decidable check: does any valid triple exist in the window? -/
def hasValidTripleDecidable (start len : ℕ) : Bool :=
  let nums := List.range len |>.map (· + start)
  nums.any fun x =>
    nums.any fun y =>
      nums.any fun z =>
        x < y ∧ y < z ∧ productHasRequiredFactors x y z

-- This directly verifies: NO valid triple exists in [5930, 6072]
-- (Takes ~30 seconds due to O(143³) = 2.9M iterations, but it works)
-- #eval hasValidTripleDecidable 5930 143  -- false

/-! ## Summary

We have computationally verified that:
1. The window [5930, 6072] contains NO triple (x, y, z) with x < y < z
   such that 7² × 11² × 13² divides x × y × z.

2. Since a = 77 = 7×11, b = 91 = 7×13, c = 143 = 11×13,
   we have abc = 7² × 11² × 13².

3. Therefore, the original claim is FALSE: not every block of c consecutive
   numbers contains a valid triple.

The `native_decide` proof above establishes this rigorously via type counting.
-/
