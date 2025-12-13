/-
  The Duality of Testing, Pentesting, and Proofs
  ===============================================

  Property Test:  Random search for CONFIRMATION
  Pentest:        Adversarial search for VIOLATION
  Formal Proof:   Universal CLOSURE of the search space
-/

namespace SecurityDuality

/-
  ## The Fundamental Duality

  Both tests and pentests are SEARCHES in input space.
  They differ in what they're searching FOR.

  Property Test (defender):
    "I'll sample inputs and check the property holds"
    Goal: Build confidence that ∀x. P(x)
    Method: Random/systematic sampling
    Success: No counterexample found (but doesn't prove anything!)

  Pentest (attacker):
    "I'll craft inputs to break the property"
    Goal: Find witness that ∃x. ¬P(x)
    Method: Adversarial/creative search
    Success: Counterexample found (PROVES insecurity!)
-/

-- A security property: "input doesn't cause overflow"
def SafeInput (input : Nat) (bufferSize : Nat) : Prop :=
  input < bufferSize

-- The UNIVERSAL security claim
def SystemSecure (bufferSize : Nat) : Prop :=
  ∀ input : Nat, input < bufferSize → SafeInput input bufferSize

-- A "property test" samples some inputs
def propertyTest (bufferSize : Nat) : Bool :=
  -- Check a few inputs...
  SafeInput 0 bufferSize ∧
  SafeInput 5 bufferSize ∧
  SafeInput 10 bufferSize
  |> decide

-- A "pentest" tries to find a VIOLATING input
-- If it returns Some x, the pentester found an exploit!
def pentest (bufferSize : Nat) : Option Nat :=
  -- Adversarial thinking: what if input ≥ bufferSize?
  if bufferSize > 0 then
    some bufferSize  -- This input would overflow!
  else
    none

#eval pentest 100  -- some 100: the pentester found input=100 breaks a buffer of size 100!

/-
  ## The Asymmetry of Evidence

  Property test passes: "I checked 1000 inputs, all safe"
    → Weak evidence (maybe input 1001 breaks it)

  Pentest succeeds: "I found input X that breaks safety"
    → STRONG evidence (constructive proof of vulnerability)

  This asymmetry is fundamental:
  - Confirming safety requires checking ALL inputs (impossible)
  - Refuting safety requires finding ONE counterexample (possible)
-/

-- A successful pentest IS a proof of insecurity
structure Vulnerability (P : α → Prop) where
  exploit : α                    -- The malicious input
  breaks : ¬P exploit            -- Proof that it violates the property

-- If pentester finds input=100 for bufferSize=100:
example : ¬SafeInput 100 100 := by
  simp [SafeInput]
  -- 100 < 100 is false, so ¬(100 < 100) is true

/-
  ## The Three Levels

  1. TESTING (Random/Systematic)
     - Samples from input space
     - Can find bugs if lucky
     - Never proves correctness
     - Complexity: O(samples)

  2. PENTESTING (Adversarial)
     - Intelligent search for violations
     - Uses domain knowledge, creativity
     - Success = constructive disproof
     - Complexity: Unbounded (human creativity)

  3. FORMAL PROOF (Universal)
     - Covers ENTIRE input space at once
     - Success = mathematical certainty
     - Makes pentesting that property IMPOSSIBLE
     - Complexity: Proof effort
-/

-- If we PROVE safety, no pentest can succeed
theorem provenSecure (n : Nat) (h : n > 0) :
    ∀ input, input < n → SafeInput input n := by
  intro input hlt
  exact hlt

-- This proof CLOSES the search space for inputs < n
-- A pentester cannot find a counterexample because NONE EXIST

/-
  ## Pentesting as Falsification

  Karl Popper: Science progresses by FALSIFICATION
  - You can never prove a theory true
  - You CAN prove it false (one counterexample)

  Software security is Popperian:
  - You can never "test security in" (infinite inputs)
  - You CAN prove insecurity (one exploit)
  - Formal verification TRANSCENDS this (proves for all inputs)
-/

/-
  ## The Inversion Structure

  Let P be a property (e.g., "no buffer overflow")

  Defender's claim:  ∀x. P(x)     "All inputs are safe"
  Attacker's goal:   ∃x. ¬P(x)    "Some input is unsafe"

  These are NEGATIONS of each other!

  ¬(∀x. P(x)) ↔ ∃x. ¬P(x)

  The defender claims universality.
  The attacker seeks an existential witness to the contrary.

  Property testing: Try to FAIL to find ∃x. ¬P(x)
  Pentesting: Try to SUCCEED in finding ∃x. ¬P(x)
-/

-- The logical duality
theorem security_duality (P : α → Prop) :
    ¬(∀ x, P x) ↔ ∃ x, ¬P x := by
  constructor
  · intro h
    by_contra hne
    push_neg at hne
    exact h hne
  · intro ⟨x, hx⟩ hall
    exact hx (hall x)

/-
  ## Types of Security Properties

  1. SAFETY: "Bad things never happen"
     ∀ execution. ¬BadState(execution)
     Pentest: Find execution reaching bad state

  2. LIVENESS: "Good things eventually happen"
     ∀ execution. ◇GoodState(execution)
     Pentest: Create execution that never reaches good state (DoS)

  3. CONFIDENTIALITY: "Secrets don't leak"
     ∀ observation. ¬LeaksSecret(observation)
     Pentest: Find observation that reveals secret

  4. INTEGRITY: "Data isn't corrupted"
     ∀ modification. Authorized(modification)
     Pentest: Find unauthorized modification path
-/

/-
  ## The Hierarchy of Assurance

  Level 0: No testing
    "Trust me bro"

  Level 1: Unit tests
    Specific inputs checked

  Level 2: Property tests (QuickCheck, fuzzing)
    Random inputs checked

  Level 3: Pentesting
    Adversarial inputs checked
    Still just sampling!

  Level 4: Bounded model checking
    All inputs up to size N checked

  Level 5: Symbolic execution
    All feasible paths explored

  Level 6: Formal verification
    Mathematical proof for ALL inputs
    PENTESTING BECOMES IMPOSSIBLE for proven properties
-/

/-
  ## The AI Revolution

  Traditional pentesting: Human creativity finds exploits
  AI-assisted pentesting: LLM + fuzzing finds more exploits

  But also:

  Traditional verification: Human writes proofs
  AI-assisted verification: LLM helps write proofs

  The race:
  - AI makes pentesting more powerful (finds more bugs)
  - AI makes proving more accessible (fixes more bugs permanently)

  Eventually: AI proves properties faster than it can find exploits
  → Shift from reactive security to proactive verification
-/

/-
  ## Example: The Classic Buffer Overflow

  Vulnerable code (conceptual):
    fn copy(src: &[u8], dst: &mut [u8]) {
      for i in 0..src.len() {
        dst[i] = src[i];  // What if src.len() > dst.len()?
      }
    }

  Property: ∀ src dst. src.len() ≤ dst.len() → safe

  Pentester: "What if I pass src with len > dst.len()?"
  → Finds the overflow

  Formal approach: PROVE bounds are checked
  → No overflow possible, pentest cannot succeed
-/

-- Safe copy with proof
def safeCopy (src : List α) (dst : List α) (h : src.length ≤ dst.length) : List α :=
  src ++ dst.drop src.length

-- The type signature ENCODES the precondition
-- You literally cannot call this function without proving src.len ≤ dst.len
-- The "pentest" (passing bad input) is rejected by the TYPE CHECKER

/-
  ## The Ultimate Insight

  A formal proof is an IMPENETRABLE SHIELD against pentesting.

  If you prove: ∀ input. Safe(input)
  Then: ∄ input. ¬Safe(input)

  The pentester's search space is EMPTY.
  Not just "we haven't found an exploit"
  But "no exploit CAN exist"

  This is the difference between:
  - "We pentested for 6 months and found nothing" (weak)
  - "We proved safety, here's the certificate" (absolute)
-/

end SecurityDuality

/-
  ## For Your String Theory Project

  The same duality applies to scientific computing:

  Test: "I ran 1000 Calabi-Yau evaluations, all looked right"
  Verification: "I proved the algorithm preserves CY invariants"

  For a Nobel Prize footnote, you want PROOFS, not tests.
  A formally verified string theory toolkit would be unprecedented.

  The genetic algorithm for CY threefolds:
  - PROVE: Fitness function respects mathematical structure
  - PROVE: Mutation operators preserve valid CY properties
  - PROVE: Selection doesn't introduce mathematical errors

  Then your results are MATHEMATICALLY GUARANTEED correct,
  not just "we didn't find bugs in testing."
-/
