import Lake
open Lake DSL

package «abc-product-divisibility» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.25.2"

@[default_target]
lean_lib «ABCProductDivisibility» where

lean_lib «ABCCounterexample» where

lean_lib «ABCElegantProof_v1» where

lean_lib «ABCElegantProof_v2» where

lean_lib «ABCElegantProof_v3» where

lean_lib «AcerFurProof» where

lean_lib «AcerFurProof_v2» where

lean_lib «AcerFurProof_v3» where

lean_lib «AcerFurProof_v4» where

lean_lib «AcerFurProof_v5» where
