import CORALean.ContSet.Polygon.Real.Operations.Mtimes

/-!
# `Polygon.times`

CORA's `@polygon/times`: `pgon = diag(M) * pgon`, so a diagonal matrix applied by `mtimes`. The
factor is a vector `v` here, the diagonal's entries; a scalar factor is `v = (s, s)`. Not
`ContSet.times`: a polygon is fixed at dimension two and has no `Mtimes` instance.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every piece scaled coordinatewise by `v`: `mtimes` at `diag(v)`. -/
def Polygon.times (v : Vec ℝ 2) (P : Polygon) : Polygon :=
  Polygon.mtimes (diagonal v) P

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
