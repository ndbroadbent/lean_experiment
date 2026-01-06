module DynamicProofs

import Data.Nat
import Decidable.Equality
import System

-- Use small numbers to avoid Nat performance issues
-- (Nat is unary - each number n is n constructors deep!)

-- A number that is proven to be >= 2
data AtLeast2 : Type where
  MkAtLeast2 : (value : Nat) -> LTE 2 value -> AtLeast2

getVal : AtLeast2 -> Nat
getVal (MkAtLeast2 v _) = v

-- A number proven to be a multiple of another
data MultipleOf : Nat -> Type where
  MkMultipleOf : (value : Nat) -> (multiplier : Nat) ->
                 value = multiplier * factor -> MultipleOf factor

getMulVal : MultipleOf f -> Nat
getMulVal (MkMultipleOf v _ _) = v

getMulK : MultipleOf f -> Nat
getMulK (MkMultipleOf _ k _) = k

-- Runtime proof construction: is n >= 2?
checkAtLeast2 : (n : Nat) -> Either String AtLeast2
checkAtLeast2 0 = Left "0 is not >= 2"
checkAtLeast2 1 = Left "1 is not >= 2"
checkAtLeast2 (S (S k)) = Right (MkAtLeast2 (S (S k)) (LTESucc (LTESucc LTEZero)))

-- Runtime proof construction: is n a multiple of factor?
checkMultipleOf : (n : Nat) -> (factor : Nat) -> Either String (MultipleOf factor)
checkMultipleOf n 0 = Left "Cannot check multiples of 0"
checkMultipleOf n factor =
  let q = n `div` factor
      r = n `mod` factor
  in case r of
       0 => case decEq n (q * factor) of
              Yes prf => Right (MkMultipleOf n q prf)
              No _ => Left "Internal error"
       _ => Left $ show n ++ " is not a multiple of " ++ show factor ++
                   " (remainder: " ++ show r ++ ")"

-- This function REQUIRES proofs - can't call without them
processVerified : {factor : Nat} -> AtLeast2 -> MultipleOf factor -> String
processVerified {factor} a2 mf =
  "SUCCESS: " ++ show (getMulVal mf) ++
  " is >= 2 AND is " ++ show (getMulK mf) ++ " x " ++ show factor

main : IO ()
main = do
  putStrLn "=== Dynamic Proof Construction ==="
  putStrLn "(Use small numbers < 20, Nat is slow)\n"

  -- Hardcoded examples to avoid stdin issues
  let test1_n = 15
  let test1_f = 5

  let test2_n = 15
  let test2_f = 7

  let test3_n = 1
  let test3_f = 3

  -- Test 1: 15, factor 5 (should pass)
  putStrLn $ "Test 1: n=" ++ show test1_n ++ ", factor=" ++ show test1_f
  case checkAtLeast2 test1_n of
    Left err => putStrLn $ "  REJECTED: " ++ err
    Right p1 => case checkMultipleOf test1_n test1_f of
      Left err => putStrLn $ "  REJECTED: " ++ err
      Right p2 => putStrLn $ "  " ++ processVerified p1 p2

  putStrLn ""

  -- Test 2: 15, factor 7 (should fail - not a multiple)
  putStrLn $ "Test 2: n=" ++ show test2_n ++ ", factor=" ++ show test2_f
  case checkAtLeast2 test2_n of
    Left err => putStrLn $ "  REJECTED: " ++ err
    Right p1 => case checkMultipleOf test2_n test2_f of
      Left err => putStrLn $ "  REJECTED: " ++ err
      Right p2 => putStrLn $ "  " ++ processVerified p1 p2

  putStrLn ""

  -- Test 3: 1, factor 3 (should fail - not >= 2)
  putStrLn $ "Test 3: n=" ++ show test3_n ++ ", factor=" ++ show test3_f
  case checkAtLeast2 test3_n of
    Left err => putStrLn $ "  REJECTED: " ++ err
    Right p1 => case checkMultipleOf test3_n test3_f of
      Left err => putStrLn $ "  REJECTED: " ++ err
      Right p2 => putStrLn $ "  " ++ processVerified p1 p2
