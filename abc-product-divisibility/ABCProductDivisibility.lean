/-
# ABC Product Divisibility Problem

Original Claim:
Let a < b < c be distinct natural numbers.
Must every block of c consecutive natural numbers contain three distinct
numbers whose product is a multiple of abc?

Answer: NO - the statement is FALSE.

This file defines the problem formally and states what we want to prove.
-/

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-! ## Problem Definitions -/

/-- A block of c consecutive natural numbers starting at n -/
def block (n c : ℕ) : Finset ℕ := Finset.Icc n (n + c - 1)

/-- The product of three numbers is divisible by abc -/
def productDivisibleByABC (x y z a b c : ℕ) : Prop :=
  (a * b * c) ∣ (x * y * z)

/-- There exist three distinct numbers in the block whose product is divisible by abc -/
def hasValidTriple (n a b c : ℕ) : Prop :=
  ∃ x y z : ℕ,
    x ∈ block n c ∧
    y ∈ block n c ∧
    z ∈ block n c ∧
    x < y ∧ y < z ∧
    productDivisibleByABC x y z a b c

/-- The original claim: for all distinct a < b < c, every block has a valid triple -/
def originalClaim : Prop :=
  ∀ a b c : ℕ, 0 < a → a < b → b < c →
    ∀ n : ℕ, 0 < n → hasValidTriple n a b c

/-! ## The Counterexample

Lavrov's counterexample uses:
- p = 7, q = 11, r = 13 (three primes)
- a = p * q = 77
- b = p * r = 91
- c = q * r = 143
- abc = p² * q² * r² = 1002001

The block [5930, 6072] (length 143) has no valid triple.
-/

def p : ℕ := 7
def q : ℕ := 11
def r : ℕ := 13

def a_val : ℕ := p * q  -- 77
def b_val : ℕ := p * r  -- 91
def c_val : ℕ := q * r  -- 143

def abc_val : ℕ := a_val * b_val * c_val  -- 1002001 = 7² × 11² × 13²

def counterexample_start : ℕ := 5930

-- Basic sanity checks
#eval a_val  -- 77
#eval b_val  -- 91
#eval c_val  -- 143
#eval abc_val  -- 901879
#eval p * p * q * q * r * r  -- 901879 (same as abc)

-- The block is [5930, 6072]
#eval counterexample_start + c_val - 1  -- 6072

/-! ## What We Want to Prove

1. The counterexample is valid: a < b < c
2. No valid triple exists in the block [5930, 6072]
3. Therefore, originalClaim is FALSE
-/

/-! ## Proof outline (completed in ABCCounterexample.lean)

1. counterexample_ordering: a_val < b_val < c_val
2. no_valid_triple: ¬hasValidTriple counterexample_start a_val b_val c_val
3. abc_conjecture_is_false: ¬originalClaim
-/
