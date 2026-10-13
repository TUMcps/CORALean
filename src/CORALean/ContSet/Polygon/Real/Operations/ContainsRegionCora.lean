import CORALean.ContSet.Polygon.Real.Polygon
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# `@polygon/contains_.m` l. 71-78 on regions

For a set operand converted to a polygon `S'`: accepts when
`withinTol(area(P), area(union(P, S')), tol)`, taken as an absolute tolerance, on the regions
the polyshapes denote.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The area of `P` equals that of `union(P, S')` within `tol`. -/
noncomputable def Polygon.containsRegionCora (tol : ℝ) (P S' : Set (Vec ℝ 2)) : Prop :=
  |(MeasureTheory.volume P).toReal - (MeasureTheory.volume (P ∪ S')).toReal| ≤ tol

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
