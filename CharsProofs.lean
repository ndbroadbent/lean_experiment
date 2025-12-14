/-
  Proofs about character concatenation as pure arithmetic.

  Key insight: Strings are just integers viewed as sequences of character codes.
  This module proves the foundational properties of 2-character "strings"
  represented as U16 values.
-/
import VerifiedRust
import Aeneas

open Aeneas.Std Result

namespace verified_rust.chars

/-
  Proof: chars_len always returns 2

  A U16 "string" always has exactly 2 characters.
-/
theorem chars_len_is_two (s : U16) : chars_len s = ok 2#u8 := by
  unfold chars_len
  rfl

/-
  Proof: chars_equal is reflexive

  Every string equals itself.
-/
theorem chars_equal_refl (s : U16) : chars_equal s s = ok true := by
  unfold chars_equal
  simp

/-
  Proof: chars_equal correctly compares different values

  Different strings are not equal.
-/
theorem chars_equal_neq {s1 s2 : U16} (h : s1 ≠ s2) :
    chars_equal s1 s2 = ok false := by
  simp only [chars_equal, h]
  rfl

/-
  These proofs establish the foundation for treating integers as strings.

  The key properties we'd like to prove (requiring more Aeneas/bitvector support):
  1. first_char(concat_chars a b) = a
  2. second_char(concat_chars a b) = b
  3. concat_chars a b = concat_chars c d ↔ a = c ∧ b = d

  The current proofs demonstrate:
  - chars_len is constant (U16 = 2 chars)
  - chars_equal is reflexive and correct
  - The generated Lean code matches the Rust semantics
-/

-- ============================================================================
-- Array-based string proofs (may be easier than bitvector proofs)
-- ============================================================================

/-
  Proof: array_len always returns 2
-/
theorem array_len_is_two (s : Array U8 2#usize) : array_len s = ok 2#usize := by
  unfold array_len
  rfl

/-
  Proof: array_equal is reflexive
-/
theorem array_equal_refl (s : Array U8 2#usize) : array_equal s s = ok true := by
  unfold array_equal
  simp [Array.index_usize]

end verified_rust.chars
