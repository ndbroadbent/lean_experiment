/-
  Example 2: String Operations and Proofs
  =======================================
  Proving properties about string operations.
-/

namespace Example2

-- Basic string concatenation
theorem hello_world : "hello" ++ " world" = "hello world" := rfl

-- String length proofs
theorem empty_string_length : "".length = 0 := rfl

theorem hello_length : "hello".length = 5 := rfl

-- Concatenation preserves the structure
theorem concat_length (s1 s2 : String) :
    (s1 ++ s2).length = s1.length + s2.length :=
  String.length_append s1 s2

-- String comparison
theorem string_eq_refl (s : String) : s == s = true := by
  simp [BEq.beq, String.beq]

-- Proving string equality is decidable
example : "abc" = "abc" := rfl
example : "abc" ≠ "def" := by decide

-- String operations with #eval to show computation
#eval "hello" ++ " world"           -- "hello world"
#eval "hello".length                 -- 5
#eval "hello".append " world"        -- "hello world"
#eval "hello world".take 5           -- "hello"
#eval "hello world".drop 6           -- "world"
#eval "HELLO".toLower                -- "hello"
#eval "hello".toUpper                -- "HELLO"

-- Substring operations
#eval "hello world".splitOn " "      -- ["hello", "world"]
#eval " ".intercalate ["a", "b", "c"] -- "a b c"

end Example2
