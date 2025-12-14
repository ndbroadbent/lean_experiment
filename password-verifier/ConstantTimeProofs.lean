/-
  ConstantTimeProofs.lean - Formal proofs about constant-time comparison

  This file proves properties about the constant-time comparison in rust/src/constant_time.rs.

  Key properties:
  1. Correctness: ct_eq_bytes returns true iff arrays are equal
  2. No early exit: The function always performs the same operations
  3. XOR/OR properties: Foundation for the algorithm

  The constant-time property is structural - the generated Lean code shows
  there are no conditionals that could cause early exit.
-/

import PasswordVerifier
import Aeneas

open Aeneas.Std Result
open password_verifier

namespace password_verifier.constant_time

-- ============================================================================
-- Helper lemmas for UScalar XOR/OR
-- ============================================================================

-- UScalar.xor is defined as ⟨ x.bv ^^^ y.bv ⟩
-- So (x ^^^ y).bv = x.bv ^^^ y.bv
@[simp] theorem U8.bv_xor (x y : U8) : (x ^^^ y).bv = x.bv ^^^ y.bv := rfl

-- Similarly for OR
@[simp] theorem U8.bv_or (x y : U8) : (x ||| y).bv = x.bv ||| y.bv := rfl

-- The zero scalar has zero bitvector
@[simp] theorem U8.bv_zero : (0#u8).bv = 0#8 := rfl

-- ============================================================================
-- XOR/OR primitive proofs
-- ============================================================================

/-
  Proof: xor_byte is self-inverse (a ^ a = 0)
  Uses BitVec.xor_self: x ^^^ x = 0
-/
theorem xor_self (a : U8) : xor_byte a a = ok 0#u8 := by
  unfold xor_byte
  simp only [ok.injEq]
  rw [U8.eq_equiv_bv_eq]
  simp only [U8.bv_xor, U8.bv_zero, BitVec.xor_self]

/-
  Proof: xor_byte with 0 is identity (a ^ 0 = a)
-/
theorem xor_zero (a : U8) : xor_byte a 0#u8 = ok a := by
  unfold xor_byte
  simp only [ok.injEq]
  rw [U8.eq_equiv_bv_eq]
  simp only [U8.bv_xor, U8.bv_zero, BitVec.xor_zero]

/-
  Proof: or_byte with 0 is identity (a | 0 = a)
-/
theorem or_zero (a : U8) : or_byte a 0#u8 = ok a := by
  unfold or_byte
  simp only [ok.injEq]
  rw [U8.eq_equiv_bv_eq]
  simp only [U8.bv_or, U8.bv_zero, BitVec.or_zero]

/-
  Proof: is_zero correctly identifies zero
-/
theorem is_zero_zero : is_zero 0#u8 = ok true := by
  unfold is_zero
  rfl

/-
  Proof: is_zero correctly identifies non-zero
-/
theorem is_zero_nonzero (a : U8) (h : a ≠ 0#u8) : is_zero a = ok false := by
  unfold is_zero
  simp [h]

-- ============================================================================
-- ct_eq_bytes correctness proofs
-- ============================================================================

-- Key lemmas for the accumulator pattern
@[simp] theorem U8.xor_self (a : U8) : a ^^^ a = 0#u8 := by
  rw [U8.eq_equiv_bv_eq]
  simp only [U8.bv_xor, U8.bv_zero, BitVec.xor_self]

@[simp] theorem U8.or_zero' (a : U8) : a ||| 0#u8 = a := by
  rw [U8.eq_equiv_bv_eq]
  simp only [U8.bv_or, U8.bv_zero, BitVec.or_zero]

@[simp] theorem U8.zero_or (a : U8) : 0#u8 ||| a = a := by
  rw [U8.eq_equiv_bv_eq]
  simp only [U8.bv_or, U8.bv_zero, BitVec.zero_or]

-- The coercion to Result for UScalar is just ok
@[simp] theorem U8.toResult_eq (x : U8) : (↑x : Result U8) = ok x := rfl

/-
  Pure functional approach: Build composable lemmas

  Key insight: Array.index_usize is a pure function.
  If we call it twice with the same arguments, we get the same result.
  This is referential transparency.
-/

-- Lemma: Binding the same Result twice and XORing gives 0 (if it succeeds)
theorem bind_U8_xor_self (f : Result U8) :
    (do let x ← f; let y ← f; ok (x ^^^ y)) = (do let _ ← f; ok 0#u8) := by
  cases f with
  | ok v => simp only [bind_tc_ok, U8.xor_self]
  | fail e => simp only [bind_tc_fail]
  | div => simp only [bind_tc_div]

-- Simplified: if f succeeds, binding twice and XORing gives 0
theorem bind_ok_xor_self (v : U8) :
    (do let x ← ok v; let y ← ok v; ok (x ^^^ y)) = ok 0#u8 := by
  simp only [bind_tc_ok, U8.xor_self]

/-
  Key lemma: In a do-block, binding the same expression twice gives same value.
  So `do let x ← e; let y ← e; f x y` can be rewritten using x = y.

  For our case: `do let i ← a[k]; let j ← a[k]; ok (i ^^^ j)`
  becomes `do let i ← a[k]; ok (i ^^^ i)` = `do let i ← a[k]; ok 0`
-/

-- The core rewrite: fuse duplicate bindings
@[simp] theorem bind_dup_xor (f : Result U8) :
    (do let x ← f; let y ← f; ok (x ^^^ y)) = (do let _ ← f; ok 0#u8) := by
  cases f <;> simp [bind_tc_ok, bind_tc_fail, bind_tc_div, U8.xor_self]

-- Basic monad law: bind then return is identity
@[simp] theorem bind_ok_id {α : Type} (r : Result α) :
    (do let x ← r; ok x) = r := by
  cases r <;> simp [bind_tc_ok, bind_tc_fail, bind_tc_div]

/-
  Proof: ct_eq_bytes returns true for equal arrays

  Strategy: Show that when both arrays are identical:
  1. Each pair a[i], a[i] XORs to 0
  2. OR-ing zeros gives 0
  3. 0 == 0 is true
-/
/-
  Core lemma: fuse two consecutive binds of the same expression
  This captures: do let x ← f; let y ← f; g x y  =  do let x ← f; g x x
-/
theorem bind_same_twice {α β : Type} (f : Result α) (g : α → α → Result β) :
    (do let x ← f; let y ← f; g x y) = (do let x ← f; g x x) := by
  cases f <;> simp [bind_tc_ok, bind_tc_fail, bind_tc_div]

-- Specialize for XOR
theorem bind_same_xor (f : Result U8) :
    (do let x ← f; let y ← f; (↑(x ^^^ y) : Result U8)) = (do let _ ← f; ok 0#u8) := by
  rw [bind_same_twice]
  cases f <;> simp [bind_tc_ok, bind_tc_fail, bind_tc_div, U8.xor_self, toResult]

-- When we bind but ignore the result, we just need the computation to succeed
@[simp] theorem bind_ignore_ok {α β : Type} (f : Result α) (x : β) :
    (do let _ ← f; ok x) = (f >>= fun _ => ok x) := rfl

-- For array access that's in bounds, it succeeds
theorem Array.index_usize_inBounds {α : Type} {n : Usize} (a : Array α n) (i : Usize)
    (h : i.val < n.val) : ∃ v, a.index_usize i = ok v := by
  simp only [Array.index_usize]
  have hlen : i.val < a.val.length := by
    have := a.property
    simp only [List.Vector.length_val] at this ⊢
    omega
  simp [List.getElem?_eq_getElem hlen]

-- Lemma: decide True = true
@[simp] theorem decide_true_eq : decide True = true := rfl

-- Lemma: chained binds that ignore results collapse if all succeed
-- We can prove this by showing what happens when index succeeds
theorem bind_ignore_chain {α β : Type} (r : Result α) (x : β) :
    (do let _ ← r; ok x) = (match r with | ok _ => ok x | fail e => fail e | div => div) := by
  cases r <;> rfl

-- Key insight: For a fixed-size array, all in-bounds accesses succeed
-- We use the existing Array.index_usize_spec with progress tactic

theorem ct_eq_bytes_refl (a : Array U8 8#usize) :
    ct_eq_bytes a a = ok true := by
  unfold ct_eq_bytes
  -- Use bind_same_twice to fuse the duplicate index calls
  simp only [bind_same_twice, U8.xor_self, U8.zero_or, toResult, bind_tc_ok]
  -- Simplify decide True = true
  simp only [decide_true_eq]
  -- Now we have: do let _ ← a.index_usize 0; ...; ok true
  -- Use progress to step through each index access
  -- Since each index 0..7 is < 8, they all succeed
  progress as ⟨ _, _ ⟩
  progress as ⟨ _, _ ⟩
  progress as ⟨ _, _ ⟩
  progress as ⟨ _, _ ⟩
  progress as ⟨ _, _ ⟩
  progress as ⟨ _, _ ⟩
  progress as ⟨ _, _ ⟩
  progress as ⟨ _, _ ⟩

/-
  The key insight for constant-time:

  Looking at the generated Lean code for ct_eq_bytes, we can see:
  1. There are NO if/then/else branches in the comparison logic
  2. Every array index is accessed unconditionally
  3. Every XOR and OR operation is performed unconditionally
  4. Only at the very end do we check if acc == 0

  This structure guarantees constant-time execution because:
  - The same sequence of operations occurs regardless of input values
  - No early exit is possible
  - The only data-dependent operation is the final equality check

  The proof that this is constant-time is STRUCTURAL:
  The generated code contains no `if` statements in the comparison loop.
  Every operation is executed regardless of input values.
-/

/-
  Theorem: The algorithm is correct.

  ct_eq_bytes(a, b) = true  iff  ∀ i. a[i] = b[i]

  The backward direction (←) is proven: equal arrays return true.
  The forward direction (→) requires proving:
    1. If result is ok true, then acc = 0
    2. If (x₀ | x₁ | ... | x₇) = 0, then each xᵢ = 0
    3. If a[i] ^^^ b[i] = 0, then a[i] = b[i]
    4. If all elements equal, arrays are equal (extensionality)
-/

/-
  Helper lemmas for the full correctness proof.
  These capture the key algebraic properties of XOR and OR.

  Note: These require bitwise reasoning that's version-dependent in Lean/Mathlib.
  The backward direction of ct_eq_bytes_correct (equal arrays → returns true)
  is fully proven above. The forward direction (returns true → equal arrays)
  uses these lemmas.
-/

-- Helper: XOR equals zero implies equality (a ⊕ b = 0 ↔ a = b)
theorem U8.xor_eq_zero_iff (a b : U8) : a ^^^ b = 0#u8 ↔ a = b := by
  constructor
  · intro h
    rw [U8.eq_equiv_bv_eq] at h ⊢
    simp only [U8.bv_xor, U8.bv_zero] at h
    -- a ^^^ b = 0 implies a = b (XOR both sides by b)
    have key : a.bv ^^^ b.bv ^^^ b.bv = 0#8 ^^^ b.bv := congrArg (· ^^^ b.bv) h
    simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero, BitVec.zero_xor] at key
    exact key
  · intro h
    rw [h]
    exact U8.xor_self b

/-
  The key insight: A BitVec n is essentially a vector of n bits.
  OR on bitvectors is pointwise OR on bits.
  For booleans: a || b = false ↔ a = false ∧ b = false

  So we can prove the bitvector property by showing each bit is false.
-/

-- Boolean OR property (trivial but foundational)
theorem Bool.or_eq_false_iff' (a b : Bool) : (a || b) = false ↔ a = false ∧ b = false := by
  cases a <;> cases b <;> simp

-- Helper: OR of zeros is zero (a ||| b = 0 ↔ a = 0 ∧ b = 0)
-- Proof strategy: A bitvector is 0 iff all its bits are false.
-- (a ||| b).bit[i] = a.bit[i] || b.bit[i]
-- If a ||| b = 0, then for all i: a.bit[i] || b.bit[i] = false
-- By Bool.or_eq_false_iff: a.bit[i] = false ∧ b.bit[i] = false
-- Therefore a = 0 and b = 0
theorem U8.or_eq_zero_iff (a b : U8) : a ||| b = 0#u8 ↔ a = 0#u8 ∧ b = 0#u8 := by
  constructor
  · intro h
    rw [U8.eq_equiv_bv_eq] at h
    simp only [U8.bv_or, U8.bv_zero] at h
    -- h : a.bv ||| b.bv = 0#8
    -- We need to show a.bv = 0 and b.bv = 0
    constructor
    · -- Show a = 0 by showing all bits are false
      rw [U8.eq_equiv_bv_eq]
      simp only [U8.bv_zero]
      -- Use BitVec.eq_of_getLsbD_eq: two bitvectors are equal iff they have the same bits
      apply BitVec.eq_of_getLsbD_eq
      intro i _hi
      -- Get the i-th bit of (a.bv ||| b.bv) = 0
      have hi : (a.bv ||| b.bv).getLsbD i = (0#8).getLsbD i := congrArg (·.getLsbD i) h
      simp only [BitVec.getLsbD_or, BitVec.getLsbD_zero] at hi
      -- hi : a.bv.getLsbD i || b.bv.getLsbD i = false
      have ⟨ha_bit, _⟩ := Bool.or_eq_false_iff' _ _ |>.mp hi
      -- Goal: a.bv.getLsbD i = (0#8).getLsbD i
      rw [ha_bit, ← BitVec.getLsbD_zero (w := 8) (i := i)]
    · -- Show b = 0 by showing all bits are false
      rw [U8.eq_equiv_bv_eq]
      simp only [U8.bv_zero]
      apply BitVec.eq_of_getLsbD_eq
      intro i _hi
      have hi : (a.bv ||| b.bv).getLsbD i = (0#8).getLsbD i := congrArg (·.getLsbD i) h
      simp only [BitVec.getLsbD_or, BitVec.getLsbD_zero] at hi
      have ⟨_, hb_bit⟩ := Bool.or_eq_false_iff' _ _ |>.mp hi
      rw [hb_bit, ← BitVec.getLsbD_zero (w := 8) (i := i)]
  · intro ⟨ha, hb⟩
    rw [ha, hb]
    rfl

-- Helper: Two Aeneas arrays are equal iff their underlying vectors are equal
theorem Array.eq_iff_val_eq {α : Type} {n : Usize} (a b : Array α n) :
    a = b ↔ a.val = b.val := by
  constructor
  · intro h; rw [h]
  · intro h; cases a; cases b; simp_all

theorem ct_eq_bytes_correct (a b : Array U8 8#usize) :
    ct_eq_bytes a b = ok true ↔ a = b := by
  constructor
  · intro h
    -- Forward direction: if ct_eq_bytes returns true, arrays are equal
    -- Unfold and use progress to step through the computation
    unfold ct_eq_bytes at h
    -- Step through all the array accesses and operations
    simp only [bind_tc_ok, toResult] at h
    -- Extract array elements using progress-like reasoning
    -- When the result is ok true, the accumulated OR must be 0
    -- Get the actual values from the array accesses
    obtain ⟨a0, ha0⟩ := Array.index_usize_inBounds a 0#usize (by scalar_tac)
    obtain ⟨b0, hb0⟩ := Array.index_usize_inBounds b 0#usize (by scalar_tac)
    obtain ⟨a1, ha1⟩ := Array.index_usize_inBounds a 1#usize (by scalar_tac)
    obtain ⟨b1, hb1⟩ := Array.index_usize_inBounds b 1#usize (by scalar_tac)
    obtain ⟨a2, ha2⟩ := Array.index_usize_inBounds a 2#usize (by scalar_tac)
    obtain ⟨b2, hb2⟩ := Array.index_usize_inBounds b 2#usize (by scalar_tac)
    obtain ⟨a3, ha3⟩ := Array.index_usize_inBounds a 3#usize (by scalar_tac)
    obtain ⟨b3, hb3⟩ := Array.index_usize_inBounds b 3#usize (by scalar_tac)
    obtain ⟨a4, ha4⟩ := Array.index_usize_inBounds a 4#usize (by scalar_tac)
    obtain ⟨b4, hb4⟩ := Array.index_usize_inBounds b 4#usize (by scalar_tac)
    obtain ⟨a5, ha5⟩ := Array.index_usize_inBounds a 5#usize (by scalar_tac)
    obtain ⟨b5, hb5⟩ := Array.index_usize_inBounds b 5#usize (by scalar_tac)
    obtain ⟨a6, ha6⟩ := Array.index_usize_inBounds a 6#usize (by scalar_tac)
    obtain ⟨b6, hb6⟩ := Array.index_usize_inBounds b 6#usize (by scalar_tac)
    obtain ⟨a7, ha7⟩ := Array.index_usize_inBounds a 7#usize (by scalar_tac)
    obtain ⟨b7, hb7⟩ := Array.index_usize_inBounds b 7#usize (by scalar_tac)
    -- Substitute all the ok values into h
    simp only [ha0, hb0, ha1, hb1, ha2, hb2, ha3, hb3, ha4, hb4, ha5, hb5, ha6, hb6, ha7, hb7, bind_tc_ok] at h
    -- Now h says: ok (acc7 = 0) = ok true where acc7 is a chain of ORs
    -- Extract the equality
    injection h with h_eq
    -- h_eq : (acc7 = 0#u8) = true, so acc7 = 0
    -- The accumulator structure (left-associative OR chain):
    -- acc7 = (((((((0 ||| x0) ||| x1) ||| x2) ||| x3) ||| x4) ||| x5) ||| x6) ||| x7
    have acc_zero : (((((((0#u8 ||| (a0 ^^^ b0)) ||| (a1 ^^^ b1)) ||| (a2 ^^^ b2)) ||| (a3 ^^^ b3)) |||
                     (a4 ^^^ b4)) ||| (a5 ^^^ b5)) ||| (a6 ^^^ b6)) ||| (a7 ^^^ b7) = 0#u8 := by
      simp only [U8.zero_or] at h_eq ⊢
      exact of_decide_eq_true h_eq
    -- Repeatedly apply or_eq_zero_iff to peel off each XOR from the right
    have ⟨acc6_zero, xor7⟩ := U8.or_eq_zero_iff _ _ |>.mp acc_zero
    have ⟨acc5_zero, xor6⟩ := U8.or_eq_zero_iff _ _ |>.mp acc6_zero
    have ⟨acc4_zero, xor5⟩ := U8.or_eq_zero_iff _ _ |>.mp acc5_zero
    have ⟨acc3_zero, xor4⟩ := U8.or_eq_zero_iff _ _ |>.mp acc4_zero
    have ⟨acc2_zero, xor3⟩ := U8.or_eq_zero_iff _ _ |>.mp acc3_zero
    have ⟨acc1_zero, xor2⟩ := U8.or_eq_zero_iff _ _ |>.mp acc2_zero
    have ⟨acc0_zero, xor1⟩ := U8.or_eq_zero_iff _ _ |>.mp acc1_zero
    -- acc0_zero : 0#u8 ||| (a0 ^^^ b0) = 0#u8
    have xor0 : a0 ^^^ b0 = 0#u8 := by simp only [U8.zero_or] at acc0_zero; exact acc0_zero
    -- Convert XOR = 0 to element equality
    have eq0 : a0 = b0 := U8.xor_eq_zero_iff _ _ |>.mp xor0
    have eq1 : a1 = b1 := U8.xor_eq_zero_iff _ _ |>.mp xor1
    have eq2 : a2 = b2 := U8.xor_eq_zero_iff _ _ |>.mp xor2
    have eq3 : a3 = b3 := U8.xor_eq_zero_iff _ _ |>.mp xor3
    have eq4 : a4 = b4 := U8.xor_eq_zero_iff _ _ |>.mp xor4
    have eq5 : a5 = b5 := U8.xor_eq_zero_iff _ _ |>.mp xor5
    have eq6 : a6 = b6 := U8.xor_eq_zero_iff _ _ |>.mp xor6
    have eq7 : a7 = b7 := U8.xor_eq_zero_iff _ _ |>.mp xor7
    -- Now use array extensionality via decidable equality
    -- Since we have eq0..eq7 showing all indexed values are equal,
    -- and the array index operations succeed consistently,
    -- we can construct the array equality.
    --
    -- Use Array.index_usize_spec to relate values to array elements
    have ha0_spec := Array.index_usize_spec a 0#usize (by scalar_tac)
    have hb0_spec := Array.index_usize_spec b 0#usize (by scalar_tac)
    have ha1_spec := Array.index_usize_spec a 1#usize (by scalar_tac)
    have hb1_spec := Array.index_usize_spec b 1#usize (by scalar_tac)
    have ha2_spec := Array.index_usize_spec a 2#usize (by scalar_tac)
    have hb2_spec := Array.index_usize_spec b 2#usize (by scalar_tac)
    have ha3_spec := Array.index_usize_spec a 3#usize (by scalar_tac)
    have hb3_spec := Array.index_usize_spec b 3#usize (by scalar_tac)
    have ha4_spec := Array.index_usize_spec a 4#usize (by scalar_tac)
    have hb4_spec := Array.index_usize_spec b 4#usize (by scalar_tac)
    have ha5_spec := Array.index_usize_spec a 5#usize (by scalar_tac)
    have hb5_spec := Array.index_usize_spec b 5#usize (by scalar_tac)
    have ha6_spec := Array.index_usize_spec a 6#usize (by scalar_tac)
    have hb6_spec := Array.index_usize_spec b 6#usize (by scalar_tac)
    have ha7_spec := Array.index_usize_spec a 7#usize (by scalar_tac)
    have hb7_spec := Array.index_usize_spec b 7#usize (by scalar_tac)
    -- Simplify: since ha0 says index_usize = ok a0, and spec gives unique value
    simp only [ha0, hb0, ha1, hb1, ha2, hb2, ha3, hb3, ha4, hb4, ha5, hb5, ha6, hb6, ha7, hb7, ok.injEq, exists_eq_left'] at ha0_spec hb0_spec ha1_spec hb1_spec ha2_spec hb2_spec ha3_spec hb3_spec ha4_spec hb4_spec ha5_spec hb5_spec ha6_spec hb6_spec ha7_spec hb7_spec
    -- Now ha0_spec : a0 = a.val[↑0#usize]!, etc.
    -- The coercion ↑0#usize evaluates to 0, so we can use native_decide or rfl
    -- Derive element equalities using the spec facts
    have elem_eq0 : a.val[0]! = b.val[0]! := by
      have : (0#usize).val = 0 := rfl
      simp only [this] at ha0_spec hb0_spec
      rw [← ha0_spec, ← hb0_spec]; exact eq0
    have elem_eq1 : a.val[1]! = b.val[1]! := by
      have : (1#usize).val = 1 := rfl
      simp only [this] at ha1_spec hb1_spec
      rw [← ha1_spec, ← hb1_spec]; exact eq1
    have elem_eq2 : a.val[2]! = b.val[2]! := by
      have : (2#usize).val = 2 := rfl
      simp only [this] at ha2_spec hb2_spec
      rw [← ha2_spec, ← hb2_spec]; exact eq2
    have elem_eq3 : a.val[3]! = b.val[3]! := by
      have : (3#usize).val = 3 := rfl
      simp only [this] at ha3_spec hb3_spec
      rw [← ha3_spec, ← hb3_spec]; exact eq3
    have elem_eq4 : a.val[4]! = b.val[4]! := by
      have : (4#usize).val = 4 := rfl
      simp only [this] at ha4_spec hb4_spec
      rw [← ha4_spec, ← hb4_spec]; exact eq4
    have elem_eq5 : a.val[5]! = b.val[5]! := by
      have : (5#usize).val = 5 := rfl
      simp only [this] at ha5_spec hb5_spec
      rw [← ha5_spec, ← hb5_spec]; exact eq5
    have elem_eq6 : a.val[6]! = b.val[6]! := by
      have : (6#usize).val = 6 := rfl
      simp only [this] at ha6_spec hb6_spec
      rw [← ha6_spec, ← hb6_spec]; exact eq6
    have elem_eq7 : a.val[7]! = b.val[7]! := by
      have : (7#usize).val = 7 := rfl
      simp only [this] at ha7_spec hb7_spec
      rw [← ha7_spec, ← hb7_spec]; exact eq7
    -- Use array extensionality via Subtype.eq_iff and List.ext_getElem!
    rw [Array.eq_iff_val_eq]
    -- Two lists are equal iff they have the same length and elements
    -- We know lengths are equal (both are 8)
    have len_eq : a.val.length = b.val.length := by
      have := a.property
      have := b.property
      omega
    apply List.ext_getElem len_eq
    intro i hi _
    -- We need to show a.val[i] = b.val[i] given the element equalities
    have ha_len : a.val.length = 8 := a.property
    have hb_len : b.val.length = 8 := b.property
    have hi8 : i < 8 := by omega
    -- Use decidability to case split on i
    match i, hi8 with
    | 0, _ => simp_all
    | 1, _ => simp_all
    | 2, _ => simp_all
    | 3, _ => simp_all
    | 4, _ => simp_all
    | 5, _ => simp_all
    | 6, _ => simp_all
    | 7, _ => simp_all
  · intro heq
    -- Backward direction: equal arrays return true
    rw [heq]
    exact ct_eq_bytes_refl b

end password_verifier.constant_time
