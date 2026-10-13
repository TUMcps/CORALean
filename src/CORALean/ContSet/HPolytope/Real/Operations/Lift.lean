import CORALean.ContSet.HPolytope.Real.Operations.Comap
import Mathlib.LinearAlgebra.Pi

/-!
# `HPolytope.lift_`

CORA's `@polytope/lift_`: `A(:,dims) = A` and zeros elsewhere, the right-hand sides unchanged.
Row `i` of the lifted polytope reads coordinate `dims k` where row `i` of `P` read `k`, which is
`comap` along the coordinate selection `x ↦ (x (dims k))ₖ`. The lifted set is unbounded in the
new coordinates, so only the halfspace form has a lift.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.lift_ (P : HPolytope (Vec ℝ n)) (dims : Fin n → Fin N) : HPolytope (Vec ℝ N) :=
  P.comap (LinearMap.funLeft ℝ ℝ dims)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
