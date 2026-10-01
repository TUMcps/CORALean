import CORALean.Examples.Bench.RandVerifyAlg
import CORALean.Examples.Bench.RandVerifyInstance

/-!
# `randverify`: one run's inputs, apart from the number type

The instance, the step `dt` (a rational string, read exactly), the algorithm, the Taylor order
`η` and the zonotope order `ρ`.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


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
