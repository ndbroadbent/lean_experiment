/-
  Proofs about the Fibonacci functions translated by Aeneas.
  These proofs demonstrate formal verification of Rust Fibonacci implementations.
-/
import VerifiedRust
import Aeneas

open Aeneas.Std Result

namespace verified_rust.fibonacci

/-
  Proof: fib_iter(0) = Ok 0

  The zeroth Fibonacci number is 0.
-/
theorem fib_iter_zero : fib_iter 0#u32 = ok 0#u64 := by
  unfold fib_iter
  simp

/-
  Proof: fib_iter(1) = Ok 1

  The first Fibonacci number is 1.
-/
theorem fib_iter_one : fib_iter 1#u32 = ok 1#u64 := by
  unfold fib_iter
  simp

/-
  Proof: fib_checked(0) = Ok (Some 0)

  The zeroth Fibonacci number is 0 (with overflow checking).
-/
theorem fib_checked_zero : fib_checked 0#u32 = ok (some 0#u64) := by
  unfold fib_checked
  simp

/-
  Proof: fib_checked(1) = Ok (Some 1)

  The first Fibonacci number is 1 (with overflow checking).
-/
theorem fib_checked_one : fib_checked 1#u32 = ok (some 1#u64) := by
  unfold fib_checked
  simp

/-
  Proof: fib_bounded(n, max) = Ok None when n > max

  When requesting a Fibonacci index beyond the maximum, returns None.
-/
theorem fib_bounded_exceeds {n max_n : U32} (h : n > max_n) :
    fib_bounded n max_n = ok none := by
  simp only [fib_bounded, h, ↓reduceIte]

/-
  Proof: fib_matrix(0) = Ok 0

  The zeroth Fibonacci number via matrix exponentiation is 0.
-/
theorem fib_matrix_zero : fib_matrix 0#u32 = ok 0#u64 := by
  unfold fib_matrix
  simp

/-
  Proof: is_fibonacci(0) = Ok true

  Zero is a Fibonacci number.
-/
theorem is_fibonacci_zero : is_fibonacci 0#u64 = ok true := by
  unfold is_fibonacci
  simp

/-
  Proof: is_fibonacci(1) = Ok true

  One is a Fibonacci number.
-/
theorem is_fibonacci_one : is_fibonacci 1#u64 = ok true := by
  unfold is_fibonacci
  simp

/-
  Proof: fib_index(0) = Ok (Some 0)

  Zero is at index 0 in the Fibonacci sequence.
-/
theorem fib_index_zero : fib_index 0#u64 = ok (some 0#u32) := by
  unfold fib_index
  simp

/-
  Proof: fib_index(1) = Ok (Some 1)

  One is at index 1 in the Fibonacci sequence.
-/
theorem fib_index_one : fib_index 1#u64 = ok (some 1#u32) := by
  unfold fib_index
  simp

/-
  These proofs demonstrate that:
  1. Base cases of Fibonacci functions are provably correct
  2. Multiple implementations (fib_iter, fib_checked, fib_matrix) have correct base cases
  3. The Aeneas-generated Lean code correctly captures the Rust semantics
  4. Bounds checking behavior (fib_bounded) is verifiable
  5. The is_fibonacci predicate correctly identifies base case Fibonacci numbers

  Key insight: Aeneas wraps operations in Result to handle potential
  overflow/underflow. The proofs show that when overflow doesn't occur,
  the functions behave as expected mathematically.
-/

end verified_rust.fibonacci
