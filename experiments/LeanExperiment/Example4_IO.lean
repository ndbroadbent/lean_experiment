/-
  Example 4: IO and Effects
  =========================
  Working with IO monad, printing, and basic effects.
-/

namespace Example4

-- IO is Lean's monad for side effects
-- IO α represents a computation that may perform IO and returns α

-- Simple IO action
def greet (name : String) : IO Unit := do
  IO.println s!"Hello, {name}!"

-- Chaining IO actions
def greetMultiple : IO Unit := do
  greet "Alice"
  greet "Bob"
  greet "Charlie"

-- IO with return values
def askQuestion : IO String := do
  IO.print "What is your name? "
  let input ← IO.getStdin
  let name ← input.getLine
  return name.trim

-- Conditional IO
def checkAge (age : Nat) : IO Unit := do
  if age >= 18 then
    IO.println "You are an adult."
  else
    IO.println "You are a minor."

-- IO with error handling using Except
def parseNat (s : String) : Except String Nat :=
  match s.trim.toNat? with
  | some n => .ok n
  | none => .error s!"Cannot parse '{s}' as a natural number"

#eval parseNat "42"      -- Except.ok 42
#eval parseNat "hello"   -- Except.error "Cannot parse 'hello' as a natural number"

-- IO with file operations (conceptual - would need actual files)
def writeToFile (path : String) (content : String) : IO Unit := do
  IO.FS.writeFile path content

def readFromFile (path : String) : IO String := do
  IO.FS.readFile path

-- Composing pure and effectful code
def pureComputation (x : Nat) : Nat := x * 2 + 1

def effectfulWithPure : IO Unit := do
  let result := pureComputation 21  -- Pure computation
  IO.println s!"The answer is {result}"  -- Effectful

-- Demonstrating that IO respects sequencing
def sequencedIO : IO Unit := do
  IO.println "First"
  IO.println "Second"
  IO.println "Third"
  -- These will always print in order

-- Working with command line arguments
def processArgs (args : List String) : IO Unit := do
  IO.println s!"Received {args.length} arguments:"
  for arg in args do
    IO.println s!"  - {arg}"

end Example4
