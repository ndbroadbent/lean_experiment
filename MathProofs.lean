/-
  Proofs about the math functions translated by Aeneas.
  These proofs demonstrate formal verification of Rust math implementations.
-/
import VerifiedRust
import Aeneas

open Aeneas.Std Result

namespace verified_rust.math

/-
  Proof: div(a, 0) = Ok None

  Division by zero returns None.
-/
theorem div_by_zero (a : U32) : div a 0#u32 = ok none := by
  unfold div
  simp

/-
  Proof: modulo(a, 0) = Ok None

  Modulo by zero returns None.
-/
theorem modulo_by_zero (a : U32) : modulo a 0#u32 = ok none := by
  unfold modulo
  simp

/-
  Proof: gcd(a, 0) = Ok a

  The GCD of any number with 0 is that number.
  This is the base case of the Euclidean algorithm.
-/
theorem gcd_zero_right (a : U32) : gcd a 0#u32 = ok a := by
  unfold gcd
  conv => lhs; unfold gcd_loop
  simp

/-
  Proof: lcm(0, b) = Ok (Some 0)

  The LCM of 0 with any number is 0.
-/
theorem lcm_zero_left (b : U32) : lcm 0#u32 b = ok (some 0#u32) := by
  unfold lcm
  simp

/-
  Proof: lcm(a, 0) = Ok (Some 0)

  The LCM of any number with 0 is 0.
-/
theorem lcm_zero_right (a : U32) (h : a ≠ 0#u32) : lcm a 0#u32 = ok (some 0#u32) := by
  simp only [lcm, h, ↓reduceIte]

/-
  Proof: is_prime(0) = Ok false

  Zero is not prime (0 < 2).
-/
theorem is_prime_zero : is_prime 0#u32 = ok false := by
  unfold is_prime
  simp

/-
  Proof: is_prime(1) = Ok false

  One is not prime (1 < 2).
-/
theorem is_prime_one : is_prime 1#u32 = ok false := by
  unfold is_prime
  simp

/-
  Proof: is_prime(2) = Ok true

  Two is prime.
-/
theorem is_prime_two : is_prime 2#u32 = ok true := by
  unfold is_prime
  simp

/-
  Proof: factorial(n) = Ok None when n > 12

  Factorial overflow protection: returns None for n > 12.
-/
theorem factorial_overflow {n : U32} (h : n > 12#u32) :
    factorial n = ok none := by
  simp only [factorial, h, ↓reduceIte]

/-
  Proof: abs_diff(a, b) = a - b when a > b
-/
theorem abs_diff_gt {a b : U32} (h : a > b) :
    abs_diff a b = a - b := by
  simp only [abs_diff, h, ↓reduceIte]

/-
  Proof: abs_diff(a, b) = b - a when ¬(a > b)
-/
theorem abs_diff_le {a b : U32} (h : ¬(a > b)) :
    abs_diff a b = b - a := by
  simp only [abs_diff, h, ↓reduceIte]

/-
  These proofs demonstrate that:
  1. Division and modulo correctly handle division by zero
  2. GCD has correct base case behavior (gcd(a, 0) = a)
  3. LCM correctly returns 0 when either argument is 0
  4. Primality checking handles small cases correctly
  5. Factorial has proper overflow protection for n > 12
  6. Absolute difference behaves correctly based on comparison

  Key insight: The Rust implementation uses Option types for operations
  that can fail (division by zero, overflow), which is captured correctly
  in the Aeneas-generated Lean code.
-/

end verified_rust.math
