import CORALean.ContSet.Polygon.Real.Polygon
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# `Polygon.regionCenter`

CORA's `polygon/center` is MATLAB's `centroid(pgon.set)`: the centroid of the region, its mean
position under the area measure. The region is what the convex pieces denote, so the centroid is
the average of the identity over it (`Polygon.regionCenter`); no formula (shoelace) and no
computation from the vertices is given. For a region of zero area (a point, a segment) the average
is `0` by Mathlib's convention where CORA's `centroid` reads the vertices (not covered).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open MeasureTheory


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The centroid of a planar region: the average of the position over it (area measure). -/
noncomputable def Polygon.regionCenter (S : Set (Vec ℝ 2)) : Vec ℝ 2 :=
  ⨍ x in S, x

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
