import Lake
open Lake DSL

package «LeanExperiment» where
  version := v!"0.1.0"

require aeneas from git
  "https://github.com/AeneasVerif/aeneas" @ "main" / "backends" / "lean"

@[default_target]
lean_lib «LeanExperiment» where

lean_lib «VerifiedRust» where
  roots := #[`VerifiedRust]

lean_lib «SimpleProofs» where
  roots := #[`SimpleProofs]

lean_lib «FibonacciProofs» where
  roots := #[`FibonacciProofs]

lean_lib «MathProofs» where
  roots := #[`MathProofs]

lean_exe «leanexperiment» where
  root := `Main
