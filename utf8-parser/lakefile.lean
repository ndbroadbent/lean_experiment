import Lake
open Lake DSL

package «Utf8Parser» where
  version := v!"0.1.0"

require aeneas from git
  "https://github.com/AeneasVerif/aeneas" @ "main" / "backends" / "lean"

@[default_target]
lean_lib «Utf8Parser» where
  roots := #[`Utf8Parser]

lean_lib «Utf8Proofs» where
  roots := #[`Utf8Proofs]
