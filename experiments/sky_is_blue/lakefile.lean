import Lake
open Lake DSL

package «SkyIsBlue» where
  version := v!"0.0.1"
  -- Computational requirements: 10^47 CPU cycles
  -- Available: your laptop
  -- Status: ❌ Need Dyson sphere

@[default_target]
lean_lib «SkyIsBlue» where
  roots := #[`SkyIsBlue]
