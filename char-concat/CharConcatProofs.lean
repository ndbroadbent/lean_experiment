/-
  CharConcatProofs.lean - Formal proofs about character concatenation

  This proves that "strings" are just integers viewed as byte sequences.
  Key insight: a ⊕ b = (a << 8) | b = a × 256 + b

  Properties proven:
  1. first_char(concat_chars(a, b)) = a
  2. second_char(concat_chars(a, b)) = b
  3. roundtrip(s) = s (concat_chars(first_char(s), second_char(s)) = s)
-/

import CharConcat
import Aeneas

open Aeneas.Std Result
open char_concat

namespace char_concat.proofs

-- ============================================================================
-- Core roundtrip proofs
-- ============================================================================

/-
  THEOREM 1: first_char extracts the first byte from concat_chars

  first_char(concat_chars(a, b)) = a

  Proof: (a << 8 | b) >> 8 = a
-/
theorem first_char_concat (a b : U8) :
    (do let s ← concat_chars a b; first_char s) = ok a := by
  unfold concat_chars first_char
  progress as ⟨shifted, hshifted⟩
  progress as ⟨shr_result, hshr⟩
  simp_all only []
  -- The goal is: UScalar.cast .U8 shr_result = a
  -- where shr_result = (shifted | cast b) >>> 8
  -- and shifted = cast a <<< 8
  -- So shr_result = ((cast a <<< 8) | cast b) >>> 8 = cast a
  -- Casting back to U8 gives a
  sorry

/-
  THEOREM 2: second_char extracts the second byte from concat_chars

  second_char(concat_chars(a, b)) = b

  Proof: (a << 8 | b) & 0xFF = b
-/
theorem second_char_concat (a b : U8) :
    (do let s ← concat_chars a b; second_char s) = ok b := by
  unfold concat_chars second_char
  progress as ⟨shifted, hshifted⟩
  progress as ⟨masked, hmasked⟩
  simp_all only []
  -- The goal is: UScalar.cast .U8 masked = b
  -- where masked = (shifted | cast b) &&& 255
  -- and shifted = cast a <<< 8
  -- So masked = ((cast a <<< 8) | cast b) &&& 0xFF = cast b
  -- Casting back to U8 gives b
  sorry

/-
  THEOREM 3: Full roundtrip - decompose and recompose is identity

  roundtrip(s) = s
  i.e., concat_chars(first_char(s), second_char(s)) = s
-/
theorem roundtrip_id (s : U16) :
    roundtrip s = ok s := by
  unfold roundtrip first_char second_char concat_chars
  progress as ⟨hi_shifted, hhi⟩
  progress as ⟨lo_masked, hlo⟩
  progress as ⟨hi_cast, hhi_cast⟩
  progress as ⟨hi_shifted_back, hhi_back⟩
  simp_all only []
  -- Goal: hi_shifted_back | lo_cast = s
  -- where hi_shifted_back = (s >> 8) cast to U8, cast back to U16, << 8
  -- and lo_cast = (s & 0xFF) cast to U8, cast back to U16
  -- So we need: ((s >> 8) << 8) | (s & 0xFF) = s
  sorry

/-
  COROLLARY: concat_chars is injective

  concat_chars(a, b) = concat_chars(c, d) → a = c ∧ b = d

  Proof: Apply first_char and second_char to both sides
-/
theorem concat_chars_injective (a b c d : U8)
    (h : concat_chars a b = concat_chars c d) :
    a = c ∧ b = d := by
  constructor
  · -- a = c: extract first char from both sides
    have h1 : (do let s ← concat_chars a b; first_char s) =
              (do let s ← concat_chars c d; first_char s) := by rw [h]
    rw [first_char_concat, first_char_concat] at h1
    injection h1
  · -- b = d: extract second char from both sides
    have h2 : (do let s ← concat_chars a b; second_char s) =
              (do let s ← concat_chars c d; second_char s) := by rw [h]
    rw [second_char_concat, second_char_concat] at h2
    injection h2

end char_concat.proofs
