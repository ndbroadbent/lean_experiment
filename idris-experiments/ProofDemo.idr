module ProofDemo

import Data.Nat

-- LTE is defined inductively:
-- data LTE : Nat -> Nat -> Type where
--   LTEZero : LTE 0 n                     -- base: 0 <= anything
--   LTESucc : LTE m n -> LTE (S m) (S n)  -- step: if m<=n then m+1<=n+1

-- This is a REAL proof that 2 <= 5
-- We build it by applying constructors
export
proof_2_lte_5 : LTE 2 5
proof_2_lte_5 = LTESucc (LTESucc LTEZero)
-- Expanding:
--   LTEZero           : LTE 0 3
--   LTESucc LTEZero   : LTE 1 4
--   LTESucc (LTESucc LTEZero) : LTE 2 5

-- This CANNOT be constructed - no valid proof exists
-- proof_5_lte_2 : LTE 5 2
-- proof_5_lte_2 = ???  -- impossible!

-- The "absurd" function handles impossible cases
-- It has type: Uninhabited a => a -> b
-- meaning: "if you give me a value of an impossible type, I can return anything"

export
demoImpossible : LTE 5 2 -> String
demoImpossible prf = absurd prf  -- We'll never reach here!

-- Why can't we construct LTE 5 2?
-- LTE 5 2 would need LTESucc applied to LTE 4 1
-- LTE 4 1 would need LTESucc applied to LTE 3 0
-- LTE 3 0 would need LTESucc applied to LTE 2 ???
-- But LTEZero only gives us LTE 0 n, not LTE (S (S m)) 0
-- And LTESucc needs LTE m n to give LTE (S m) (S n), can't decrease second arg

-- The dependent pair (k ** value = k * factor) is also a real proof:
-- It requires you to provide:
-- 1. A witness k
-- 2. A proof term showing value equals k * factor

export
proof_15_multiple_of_3 : (k : Nat ** 15 = k * 3)
proof_15_multiple_of_3 = (5 ** Refl)
-- Refl only typechecks when both sides are definitionally equal
-- Idris computes: 5 * 3 = 15, so "15 = 15" and Refl works

-- This won't typecheck - 15 ≠ 4 * 3
-- bad_proof : (k : Nat ** 15 = k * 3)
-- bad_proof = (4 ** Refl)  -- Error! 15 ≠ 12

-- What if we try to lie?
-- export
-- lie : (k : Nat ** 15 = k * 7)
-- lie = (2 ** Refl)  -- Error! 15 ≠ 14
-- lie = (3 ** Refl)  -- Error! 15 ≠ 21
-- No valid k exists!
