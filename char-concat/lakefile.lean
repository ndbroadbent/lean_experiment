import Lake
open Lake DSL

package «char-concat» where
  version := v!"0.1.0"

require aeneas from git
  "https://github.com/aeneasverif/aeneas" @ "main" / "backends" / "lean"

@[default_target]
lean_lib «CharConcat» where

lean_lib «CharConcatProofs» where
