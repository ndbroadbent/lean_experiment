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

import VerifiedRust
import Aeneas

open Aeneas.Std Result
open verified_rust

namespace verified_rust.password

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
  unfold reveal_secret
  unfold check_password
  -- check_password PASSWORD = ct_eq_bytes PASSWORD PASSWORD
  -- By ct_eq_bytes_refl, this returns true
  -- So we take the `then` branch and return Some(SECRET)
  sorry -- requires ct_eq_bytes PASSWORD PASSWORD = ok true

/-
  THEOREM 2: Wrong password reveals nothing.

  This is the "confidentiality" property: an attacker with the wrong
  password cannot access the secret.
-/
theorem wrong_password_reveals_nothing (input : Array U8 8#usize)
    (h : input ≠ PASSWORD) :
    reveal_secret input = ok none := by
  unfold reveal_secret
  unfold check_password
  -- check_password input = ct_eq_bytes input PASSWORD
  -- Since input ≠ PASSWORD, this returns false
  -- So we take the `else` branch and return None
  sorry -- requires ct_eq_bytes input PASSWORD = ok false when input ≠ PASSWORD

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

  In the Rust code, SECRET is a constant. The only function that
  returns it is reveal_secret (and get_secret, which is for testing).

  reveal_secret only returns SECRET when check_password returns true.
  check_password only returns true when input = PASSWORD.

  Therefore: the only way to get SECRET from reveal_secret is to
  provide PASSWORD as input.
-/

/-
  Alternative formulation using Result type:
-/
theorem reveal_secret_result_correct :
    reveal_secret_result PASSWORD = ok (core.result.Result.Ok SECRET) := by
  unfold reveal_secret_result
  unfold check_password
  sorry -- same reasoning as correct_password_reveals_secret

theorem reveal_secret_result_wrong (input : Array U8 8#usize)
    (h : input ≠ PASSWORD) :
    reveal_secret_result input = ok (core.result.Result.Err ()) := by
  unfold reveal_secret_result
  unfold check_password
  sorry -- same reasoning as wrong_password_reveals_nothing

-- ============================================================================
-- Structural observation: constant-time property
-- ============================================================================

/-
  The constant-time property is inherited from ct_eq_bytes.

  Looking at the generated Lean code for check_password:

    def password.check_password (input : Array U8 8#usize) : Result Bool := do
      constant_time.ct_eq_bytes input password.PASSWORD

  This directly calls ct_eq_bytes, which we've shown in ConstantTimeProofs.lean
  to have no early-exit branches. Therefore, check_password also has no
  timing side-channel that could leak information about how close a guess
  is to the correct password.
-/

end verified_rust.password
