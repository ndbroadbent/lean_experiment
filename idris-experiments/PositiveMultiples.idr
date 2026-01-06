module PositiveMultiples

import Data.Nat

-- A refined type: a number that is both >= 2 AND a multiple of some factor
-- This bundles the VALUE with PROOFS of its properties
public export
record PositiveMultiple (factor : Nat) where
  constructor MkPosMultiple
  value : Nat
  gtOne : LTE 2 value
  isMultiple : (k : Nat ** value = k * factor)

-- Helper: 2 <= a * b when 2 <= a and 2 <= b
-- For all cases where a >= 2 and b >= 2, the product is >= 4 >= 2
export
lte2Product : (a, b : Nat) -> LTE 2 a -> LTE 2 b -> LTE 2 (a * b)
lte2Product 0 _ pa _ = absurd pa
lte2Product 1 _ pa _ = absurd (succNotLTEpred pa)
lte2Product _ 0 _ pb = absurd pb
lte2Product _ 1 _ pb = absurd (succNotLTEpred pb)
lte2Product (S (S a')) (S (S b')) _ _ = LTESucc (LTESucc LTEZero)

-- Multiply two positive numbers (both >= 2)
-- Returns a PositiveMultiple proving the result has the required properties
export
multiplyPositives : (a : Nat) -> (b : Nat) ->
                    (pa : LTE 2 a) -> (pb : LTE 2 b) ->
                    PositiveMultiple b
multiplyPositives a b pa pb =
  MkPosMultiple (a * b) (lte2Product a b pa pb) (a ** Refl)

-- A function that ONLY accepts a PositiveMultiple
-- This demonstrates dependent types: the input MUST satisfy the algebraic properties
export
processMultiple : {factor : Nat} -> PositiveMultiple factor -> String
processMultiple (MkPosMultiple v _ _) =
  "Value: " ++ show v ++ " is a multiple of the factor and is >= 2"

-- Even more restrictive: only accept multiples of a SPECIFIC number (e.g., 7)
-- You CANNOT pass a PositiveMultiple 3 to this function!
export
processMultipleOf7 : PositiveMultiple 7 -> Nat
processMultipleOf7 (MkPosMultiple v _ _) = v

-- Example usage - the proofs are computed at compile time
export
example1 : PositiveMultiple 3
example1 = multiplyPositives 5 3 (LTESucc (LTESucc LTEZero)) (LTESucc (LTESucc LTEZero))
-- 5 * 3 = 15, which is a multiple of 3 and >= 2

export
example2 : PositiveMultiple 7
example2 = multiplyPositives 4 7 (LTESucc (LTESucc LTEZero)) (LTESucc (LTESucc LTEZero))
-- 4 * 7 = 28, which is a multiple of 7 and >= 2

-- These work because the types match
export
exampleUsage : String
exampleUsage = processMultiple example1

export
exampleUsage7 : Nat
exampleUsage7 = processMultipleOf7 example2

-- This would NOT compile - type mismatch!
-- badExample : Nat
-- badExample = processMultipleOf7 example1  -- example1 is PositiveMultiple 3, not 7!

-- The type signature itself is documentation:
-- "This function requires a number that is >= 2 AND divisible by factor"
export
onlyAcceptsRefinedType : {factor : Nat} -> PositiveMultiple factor -> String
onlyAcceptsRefinedType {factor} (MkPosMultiple v _ _) =
  "Received " ++ show v ++ " which is guaranteed to be >= 2 and divisible by " ++ show factor

-- Extract the value - the proofs are erased at runtime but checked at compile time
export
getValue : PositiveMultiple factor -> Nat
getValue (MkPosMultiple v _ _) = v

-- A consumer that requires BOTH properties: multiple of 5 AND the value itself
-- This shows how dependent types let us express precise constraints
export
requiresMultOf5 : (pm : PositiveMultiple 5) -> (p : LTE 10 (getValue pm)) -> String
requiresMultOf5 pm _ = "Value " ++ show (getValue pm) ++ " is >= 10 and a multiple of 5"
