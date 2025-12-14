/-
  Example 3: Option Monad and Functional Programming
  ===================================================
  Working with Option (Maybe), monadic operations, and proofs.
-/

namespace Example3

-- Option is Lean's Maybe type
-- Option α = none | some α

-- Basic Option operations
def safeDivide (a b : Nat) : Option Nat :=
  if b = 0 then none else some (a / b)

#eval safeDivide 10 2   -- some 5
#eval safeDivide 10 0   -- none

-- Proving properties about Option
theorem some_is_not_none (x : α) : some x ≠ none := by
  intro h
  cases h

theorem none_is_not_some (x : α) : none ≠ some x := by
  intro h
  cases h

-- Option.map preserves some
theorem map_some (f : α → β) (x : α) :
    Option.map f (some x) = some (f x) := rfl

-- Option.bind (monadic bind)
theorem bind_some (x : α) (f : α → Option β) :
    (some x).bind f = f x := rfl

theorem bind_none (f : α → Option β) :
    (none : Option α).bind f = none := rfl

-- Using do-notation (monadic syntax)
def pipeline : Option Nat := do
  let a ← some 10
  let b ← some 2
  safeDivide a b

#eval pipeline  -- some 5

def failingPipeline : Option Nat := do
  let a ← some 10
  let b ← none  -- This makes the whole thing fail
  safeDivide a b

#eval failingPipeline  -- none

-- List monad (nondeterminism)
def listExample : List Nat := do
  let x ← [1, 2, 3]
  let y ← [10, 100]
  return x * y

#eval listExample  -- [10, 100, 20, 200, 30, 300]

-- Proving monad laws for Option
-- Left identity: return a >>= f ≡ f a
theorem option_left_identity (a : α) (f : α → Option β) :
    (some a).bind f = f a := rfl

-- Right identity: m >>= return ≡ m
theorem option_right_identity (m : Option α) :
    m.bind some = m := by
  cases m <;> rfl

-- Associativity: (m >>= f) >>= g ≡ m >>= (λx. f x >>= g)
theorem option_associativity (m : Option α) (f : α → Option β) (g : β → Option γ) :
    (m.bind f).bind g = m.bind (fun x => (f x).bind g) := by
  cases m <;> rfl

end Example3
