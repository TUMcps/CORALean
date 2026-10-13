import CORALean.ContDynamics.NonlinearSys.Definitions.PolyReach

/-!
# CORA's `options` for the polynomialization algorithm

`Δt` (CORA's `timeStep`, the paper's `r`) and `η` (CORA's `taylorTerms`). The rest is the
paper's and not CORA's: `UΔ` the input set's deviation, `taylor`, `combine`, `post`
the derivative bundle and the two set operations lines 3, 9 and 13 stand for,
`sub`, `enlarge` and `fuel` the abstraction-error loop's, and `K` how many
iterations `reach` unions.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       30-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet


-- ========================================  MAIN TYPE  ========================================= --

/-- The options of `NonlinearSys.polyReachReach`. -/
structure NonlinearSys.PolyReachOptions (n m o : ℕ) where
  Δt : ℝ
  η : ℕ
  UΔ : PolyZonotope (Vec ℝ m)
  taylor : NonlinearSys.PolyTaylor n m o
  combine : PolyZonotope (Vec ℝ n) → PolyZonotope (Vec ℝ m) → PolyZonotope (Vec ℝ o)
  post : NonlinearSys.PolyPost n m o
  sub : PolyZonotope (Vec ℝ n) → PolyZonotope (Vec ℝ n) → Bool
  enlarge : PolyZonotope (Vec ℝ n) → PolyZonotope (Vec ℝ n)
  fuel : ℕ
  K : ℕ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
