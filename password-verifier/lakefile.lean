import Lake
open Lake DSL

package «PasswordVerifier» where
  version := v!"0.1.0"

require aeneas from git
  "https://github.com/AeneasVerif/aeneas" @ "main" / "backends" / "lean"

@[default_target]
lean_lib «PasswordVerifier» where
  roots := #[`PasswordVerifier]

lean_lib «PasswordProofs» where
  roots := #[`PasswordProofs]

lean_lib «ConstantTimeProofs» where
  roots := #[`ConstantTimeProofs]
