/-
  PasswordProofs.lean - Formal proofs about password-protected secret revelation

  This file proves the core security properties:
  1. Correct password → secret is revealed
  2. Wrong password → secret is NOT revealed
  3. The only way to get the secret is with the correct password

  These proofs establish that the password checker is correct and secure
  against logical attacks (though not against side-channel attacks at the
  hardware level).
-/

import PasswordVerifier
import ConstantTimeProofs
import Aeneas

open Aeneas.Std Result
open password_verifier

namespace password_verifier.password

-- ============================================================================
-- Constants (these are the actual values from the Rust code)
-- ============================================================================

/-
  The secret is: "The key!" = [84, 104, 101, 32, 107, 101, 121, 33]
  The password is: "hunter42" = [104, 117, 110, 116, 101, 114, 52, 50]
-/

-- ============================================================================
-- Core security proofs
-- ============================================================================

/-
  THEOREM 1: Correct password reveals the secret.

  This is the "availability" property: a legitimate user with the
  correct password can always access the secret.
-/
theorem correct_password_reveals_secret :
    reveal_secret PASSWORD = ok (some SECRET) := by
  unfold reveal_secret check_password
  -- ct_eq_bytes PASSWORD PASSWORD = ok true by ct_eq_bytes_refl
  simp only [constant_time.ct_eq_bytes_refl, bind_tc_ok]

/-
  THEOREM 2: Wrong password reveals nothing.

  This is the "confidentiality" property: an attacker with the wrong
  password cannot access the secret.
-/
-- Helper: ct_eq_bytes returns ok false when arrays differ
theorem ct_eq_bytes_neq (a b : Array U8 8#usize) (h : a ≠ b) :
    constant_time.ct_eq_bytes a b = ok false := by
  -- We know ct_eq_bytes_correct: ct_eq_bytes a b = ok true ↔ a = b
  -- Since a ≠ b, the result cannot be ok true
  -- We need to show it's ok false (not fail or div)
  -- First, ct_eq_bytes always succeeds for valid arrays (all indices < 8)
  unfold constant_time.ct_eq_bytes
  simp only [bind_tc_ok, toResult]
  -- Step through array accesses - all succeed because indices are in bounds
  progress as ⟨a0, _⟩
  progress as ⟨b0, _⟩
  progress as ⟨a1, _⟩
  progress as ⟨b1, _⟩
  progress as ⟨a2, _⟩
  progress as ⟨b2, _⟩
  progress as ⟨a3, _⟩
  progress as ⟨b3, _⟩
  progress as ⟨a4, _⟩
  progress as ⟨b4, _⟩
  progress as ⟨a5, _⟩
  progress as ⟨b5, _⟩
  progress as ⟨a6, _⟩
  progress as ⟨b6, _⟩
  progress as ⟨a7, _⟩
  progress as ⟨b7, _⟩
  simp only [ok.injEq]
  -- Now we need to show the accumulator != 0 (so decide gives false)
  -- Use contrapositive: if result were true, then a = b, contradiction
  by_contra h_eq
  push_neg at h_eq
  -- h_eq says the accumulated OR equals 0
  have h_true : constant_time.ct_eq_bytes a b = ok true := by
    unfold constant_time.ct_eq_bytes
    simp_all only [bind_tc_ok, toResult]
  have := constant_time.ct_eq_bytes_correct a b |>.mp h_true
  exact h this

theorem wrong_password_reveals_nothing (input : Array U8 8#usize)
    (h : input ≠ PASSWORD) :
    reveal_secret input = ok none := by
  unfold reveal_secret check_password
  simp only [ct_eq_bytes_neq input PASSWORD h, bind_tc_ok]

/-
  THEOREM 3: The secret is only revealed with the correct password.

  This combines theorems 1 and 2: reveal_secret returns Some(SECRET)
  if and only if the input equals PASSWORD.
-/
theorem secret_iff_correct_password (input : Array U8 8#usize) :
    reveal_secret input = ok (some SECRET) ↔ input = PASSWORD := by
  constructor
  · -- If secret is revealed, password must be correct
    intro h
    -- Contrapositive: if input ≠ PASSWORD, then reveal_secret input = ok none
    by_contra hne
    have := wrong_password_reveals_nothing input hne
    -- But we have h : reveal_secret input = ok (some SECRET)
    -- This contradicts reveal_secret input = ok none
    simp_all
  · -- If password is correct, secret is revealed
    intro heq
    rw [heq]
    exact correct_password_reveals_secret

-- ============================================================================
-- No other path to secret
-- ============================================================================

/-
  COROLLARY: The only way to obtain SECRET is through reveal_secret
  with the correct password.

  reveal_secret only returns SECRET when check_password returns true.
  check_password only returns true when input = PASSWORD.

  Therefore: the only way to get SECRET from reveal_secret is to
  provide PASSWORD as input.

  The constant-time property is inherited from ct_eq_bytes - there are
  no early-exit branches in the comparison, preventing timing attacks.
-/

end password_verifier.password
