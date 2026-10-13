import CORALean.Examples.Bench.RandVerifyAlg
import CORALean.Examples.Bench.RandVerifyInstance

/-!
# `randverify`: one run's inputs, apart from the number type

The instance, the step `dt` (a rational string, read exactly), the algorithm, the Taylor order
`η` and the zonotope order `ρ`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench


-- ========================================  MAIN TYPE  ========================================= --

structure RandJob where
  inst : RandInstance
  dt : String
  alg : RandAlg
  eta : ℕ
  rho : ℕ

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
