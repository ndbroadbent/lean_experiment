/-
  Category Theory and the Nature of Testing vs Verification
  =========================================================

  Exploring the relationship between:
  - Unit tests (point-wise checks)
  - Properties (universal statements)
  - Formal proofs (constructive evidence)

  Note: For full category theory, add Mathlib to lakefile.toml:
    [[require]]
    name = "mathlib"
    scope = "leanprover-community"
    rev = "master"
-/

namespace TestVsProof

/-
  ## What is a Unit Test?

  A unit test is a POINT in the function's graph:
    test: f(x₀) = y₀

  It samples ONE input-output pair and checks equality.

  A test suite is a FINITE SET of such points:
    { (x₁, y₁), (x₂, y₂), ..., (xₙ, yₙ) }

  This gives us EVIDENCE but not PROOF.
-/

-- A "test" as a decidable proposition at a specific point
def UnitTest (f : α → β) [DecidableEq β] (input : α) (expected : β) : Bool :=
  f input == expected

-- Example: testing that double(3) = 6
def double (n : Nat) : Nat := n * 2

#eval UnitTest double 3 6   -- true
#eval UnitTest double 5 10  -- true
#eval UnitTest double 0 0   -- true

/-
  ## What is a Property/Specification?

  A property is a UNIVERSAL statement about ALL inputs:
    ∀x, P(f(x))

  This covers the ENTIRE domain, not just sampled points.
-/

-- The PROPERTY that double actually doubles
theorem double_spec : ∀ n : Nat, double n = n * 2 := by
  intro n
  rfl  -- trivially true by definition

-- A more interesting property: double is always even
theorem double_always_even : ∀ n : Nat, double n % 2 = 0 := by
  intro n
  simp [double, Nat.mul_mod_right]

/-
  ## The Fundamental Difference

  Test:  f(3) = 6              -- ONE witness, could be coincidence
  Proof: ∀n, f(n) = 2*n        -- ALL cases, by construction

  The test is like looking through a keyhole.
  The proof is like having the blueprint of the room.
-/

/-
  ## Can You "Formally Verify" a Unit Test?

  Yes! A unit test becomes a theorem about a specific point.
  But this is trivial - it's just computation.
-/

-- These are "verified unit tests" - trivially true by evaluation
theorem test_double_3 : double 3 = 6 := rfl
theorem test_double_5 : double 5 = 10 := rfl
theorem test_double_0 : double 0 = 0 := rfl

/-
  ## The Nature of the "Bit"

  You asked: Is a test a "hyper-function" that reduces to a validity bit?

  YES, precisely! In type theory terms:

  A test is: (f : A → B) × (x : A) × (y : B) → Bool
           = "given f, x, y, does f(x) = y?"

  The result is a DECISION, not a PROOF.

  - Bool has two values: true, false
  - But Prop (propositions) have PROOF WITNESSES

  The difference:
  - `true : Bool` carries no information beyond "yes"
  - `proof : P` carries the STRUCTURE of WHY P holds
-/

-- The test result: just true/false, no information about WHY
#check (true : Bool)

-- The proof: actual evidence, a TERM that witnesses the equality
#check (rfl : double 3 = 6)

/-
  ## Curry-Howard Correspondence: Proofs ARE Programs

  Types    ↔  Propositions
  Programs ↔  Proofs

  The type `double 3 = 6` is a PROPOSITION (a type with at most one inhabitant).
  The term `rfl` is a PROOF (a program that constructs a witness).

  A test EVALUATES to true/false.
  A proof CONSTRUCTS a witness term.
-/

-- The test: computational check, throws away structure
def runTest : Bool := double 3 == 6

-- The proof: a TERM of type `double 3 = 6`
def proofTerm : double 3 = 6 := rfl

/-
  ## The "Bit" is the Shadow of the Proof

  Consider:
  - A proof `p : P` exists in a rich type
  - Deciding `P` yields `true : Bool` or `false : Bool`

  The Bool is the PROJECTION of the proof onto {0, 1}.
  It loses all structure but preserves the yes/no answer.

  Unit tests live in Bool-land: they give answers.
  Proofs live in Type-land: they give REASONS.
-/

-- Decision: projects proof to Bool
def decideDouble3 : Decidable (double 3 = 6) := inferInstance

#eval (if h : double 3 = 6 then true else false)  -- true (the bit)
-- But we also have `h : double 3 = 6` in the true branch (the proof)

/-
  ## From Tests to Properties: The AI Opportunity

  Given tests: { f(0)=0, f(1)=2, f(2)=4, f(3)=6 }

  AI can CONJECTURE: "Maybe ∀n, f(n) = 2n?"

  Then ATTEMPT a proof. If it succeeds, the tests were
  actually sampling from a true universal property!

  This is SPECIFICATION MINING - inferring specs from examples.
-/

-- Simulating what AI might do:
-- Given: test_f_0 : f 0 = 0, test_f_1 : f 1 = 2, test_f_2 : f 2 = 4
-- Conjecture: ∀ n, f n = 2 * n
-- Attempt proof...

-- If the proof goes through, ONE theorem replaces INFINITELY many tests!
theorem double_universal : ∀ n, double n = 2 * n := by
  intro n
  simp [double]
  ring

/-
  ## Category Theory Perspective (Conceptual)

  In category theory:
  - Objects are types
  - Morphisms are functions
  - Functors map categories preserving structure

  A test checks: "Does f ∘ g = h at point x?"
  A proof shows: "f ∘ g = h for ALL points"

  Tests verify specific diagram instances.
  Proofs verify that diagrams commute universally.

  The magic: Once you prove a functor is well-defined,
  you get INFINITELY many specific equalities for free.
-/

end TestVsProof

/-
  ## Building Our Own Mini Category Theory
-/

namespace MiniCat

-- A category is:
-- 1. Objects (a type)
-- 2. Morphisms between objects
-- 3. Identity morphisms
-- 4. Composition
-- 5. Laws: identity and associativity

class Category (Obj : Type) where
  Hom : Obj → Obj → Type                           -- Morphisms
  id : (A : Obj) → Hom A A                         -- Identity
  comp : {A B C : Obj} → Hom B C → Hom A B → Hom A C  -- Composition (g ∘ f)
  id_left : ∀ {A B} (f : Hom A B), comp (id B) f = f
  id_right : ∀ {A B} (f : Hom A B), comp f (id A) = f
  assoc : ∀ {A B C D} (f : Hom A B) (g : Hom B C) (h : Hom C D),
    comp h (comp g f) = comp (comp h g) f

-- Example: Type forms a category where morphisms are functions
instance : Category Type where
  Hom A B := A → B
  id _ := fun x => x
  comp g f := fun x => g (f x)
  id_left _ := rfl
  id_right _ := rfl
  assoc _ _ _ := rfl

-- A FUNCTOR between categories
structure Functor (C D : Type) [Category C] [Category D] where
  obj : C → D
  map : {A B : C} → Category.Hom A B → Category.Hom (obj A) (obj B)
  map_id : ∀ A, map (Category.id A) = Category.id (obj A)
  map_comp : ∀ {A B C} (f : Category.Hom A B) (g : Category.Hom B C),
    map (Category.comp g f) = Category.comp (map g) (map f)

/-
  The functor laws (map_id, map_comp) are UNIVERSAL properties.

  Testing a functor: check map_id for SOME object A
  Proving a functor: show map_id for ALL objects A

  The proof gives you infinitely many tests for free.
-/

end MiniCat

/-
  ## The Deep Insight

  A TEST says: "I checked some points, no bugs found"
  A PROOF says: "Here is WHY it works for ALL points"

  Tests are NECESSARY (catch silly mistakes quickly)
  Proofs are SUFFICIENT (guarantee correctness forever)

  The "bit" of a test is ephemeral - it reflects a single run.
  The "type" of a proof is eternal - it's a mathematical certificate.

  ## The Hierarchy

  1. No tests      → "Trust me bro"
  2. Unit tests    → Point samples from the behavior
  3. Property tests → Random samples, more coverage
  4. Symbolic exec  → All paths through code
  5. Formal proof   → Mathematical certainty

  AI can help move UP this hierarchy by:
  - Inferring properties from test suites
  - Generating proof attempts
  - Finding minimal test suites that characterize behavior
  - Identifying what properties WOULD need to be proven

  ## The Future

  With tools like Aeneas + AI:
  - Write Rust code with tests
  - AI conjectures properties from tests
  - Aeneas extracts to Lean
  - AI attempts proofs
  - Human reviews and refines
  - Eventually: verified code with NO tests needed

  The tests become SCAFFOLDING for discovering the real properties.
  Once proved, the scaffolding can be removed.
-/
