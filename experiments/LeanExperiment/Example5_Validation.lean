/-
  Example 5: Input Validation with Proofs
  ========================================
  Validating input, proving bounds, and safe string operations.

  This example shows how Lean can verify properties about user input:
  - What happens when a user types "hello" → concatenates to " world"
  - What happens if they type something else
  - Limiting input to 10 characters
-/

namespace Example5

/-
  A validated string that is guaranteed to be at most `maxLen` characters.
  The proof `h` witnesses that the length bound holds.
-/
structure BoundedString (maxLen : Nat) where
  value : String
  h : value.length ≤ maxLen

-- Smart constructor that validates at runtime but produces a proof
def mkBoundedString (maxLen : Nat) (s : String) : Option (BoundedString maxLen) :=
  if h : s.length ≤ maxLen then
    some ⟨s, h⟩
  else
    none

-- Example: Creating bounded strings
#eval mkBoundedString 10 "hello"        -- some ⟨"hello", _⟩
#eval mkBoundedString 10 "hello world"  -- none (11 chars > 10)
#eval mkBoundedString 10 "0123456789"   -- some (exactly 10)

/-
  Process input: if user types "hello", concatenate " world"
  Otherwise, echo with a prefix. Enforces 10-char limit.
-/
def processInput (input : String) : Option String :=
  if input.length > 10 then
    none  -- Reject inputs over 10 characters
  else if input == "hello" then
    some (input ++ " world")  -- Special case for "hello"
  else
    some ("You typed: " ++ input)

#eval processInput "hello"        -- some "hello world"
#eval processInput "hi"           -- some "You typed: hi"
#eval processInput "this is long" -- none (too long)

/-
  A more sophisticated version with proofs about the output
-/
structure ValidatedInput where
  original : String
  originalLengthBound : original.length ≤ 10
  processed : String

def validateAndProcess (input : String) : Option ValidatedInput :=
  if h : input.length ≤ 10 then
    let processed := if input == "hello"
                     then input ++ " world"
                     else "You typed: " ++ input
    some ⟨input, h, processed⟩
  else
    none

-- Theorem: If input is "hello" and valid, output ends with " world"
theorem hello_gets_world (h : validateAndProcess "hello" = some v) :
    v.processed.endsWith " world" = true := by
  simp [validateAndProcess] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  native_decide

-- Theorem: Valid inputs never return none if length ≤ 10
theorem valid_length_succeeds (s : String) (h : s.length ≤ 10) :
    (validateAndProcess s).isSome = true := by
  simp [validateAndProcess, h]

/-
  A version with Except for better error messages
-/
inductive ValidationError
  | TooLong (actual : Nat) (max : Nat)
  | Empty

def validateInput (input : String) : Except ValidationError String :=
  if input.isEmpty then
    .error .Empty
  else if input.length > 10 then
    .error (.TooLong input.length 10)
  else if input == "hello" then
    .ok (input ++ " world")
  else
    .ok ("You typed: " ++ input)

-- Error message generation
def ValidationError.message : ValidationError → String
  | .TooLong actual max => s!"Input too long: {actual} chars (max {max})"
  | .Empty => "Input cannot be empty"

#eval validateInput ""                -- .error .Empty
#eval validateInput "hello"           -- .ok "hello world"
#eval validateInput "test"            -- .ok "You typed: test"
#eval validateInput "this is way too long"  -- .error (.TooLong 20 10)

/-
  Dependent types: A string indexed by its actual length
-/
structure SizedString (n : Nat) where
  value : String
  h : value.length = n

def mkSizedString (s : String) : SizedString s.length :=
  ⟨s, rfl⟩

-- Concatenation preserves size properties
def concatSized (s1 : SizedString n) (s2 : SizedString m) :
    SizedString (n + m) := by
  refine ⟨s1.value ++ s2.value, ?_⟩
  rw [String.length_append, s1.h, s2.h]

/-
  Full example: A validated greeting function with IO
-/
def greetWithValidation (input : String) : IO Unit := do
  match validateInput input with
  | .ok result =>
    IO.println s!"Success: {result}"
  | .error err =>
    IO.eprintln s!"Error: {err.message}"

end Example5
