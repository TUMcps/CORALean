import CORALean.ContSet.Polygon.Real.Operations.Times
import CORALean.ContSet.Polygon.Real.Theorems.MtimesExact

/-!
# `Polygon.times` is the image

`mtimes_exact` at the diagonal matrix: the image of the polygon under `x ↦ (v i * x i)`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.times_exact (v : Vec ℝ 2) (P : Polygon) :
    (diagonal v *ᵥ ·) '' ContSet.construct P = ContSet.construct (Polygon.times v P) :=
  Polygon.mtimes_exact (diagonal v) P

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
