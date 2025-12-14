/-
  Example 1: Basic Arithmetic Proofs
  ==================================
  Proving 1 + 1 = 2 and other fundamental arithmetic facts.
-/

namespace Example1

-- The simplest proof: 1 + 1 = 2
-- `rfl` (reflexivity) works because Lean computes both sides and sees they're equal
theorem one_plus_one : 1 + 1 = 2 := rfl

-- We can also prove it more explicitly
theorem one_plus_one_explicit : 1 + 1 = 2 := by
  -- `native_decide` uses native computation to verify
  native_decide

-- Some more arithmetic proofs
theorem two_times_two : 2 * 2 = 4 := rfl

theorem addition_is_commutative (a b : Nat) : a + b = b + a := Nat.add_comm a b

theorem multiplication_distributes (a b c : Nat) : a * (b + c) = a * b + a * c :=
  Nat.mul_add a b c

-- A computed example showing Lean evaluates at compile time
#eval 1 + 1  -- Output: 2

-- Check that our theorem type-checks
#check one_plus_one

-- Print info about the theorem
#print one_plus_one

end Example1
