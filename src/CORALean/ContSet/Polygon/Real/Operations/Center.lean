module

public import CORALean.ContSet.Polygon.Real.Operations.RegionCenter
public import CORALean.ContSet.VPolytope.Real.Instances

@[expose] public section

/-!
# `Polygon.center`

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

/-- The centroid of the region a polygon denotes. -/
noncomputable def Polygon.center (P : Polygon) : Vec ℝ 2 :=
  Polygon.regionCenter (ContSet.construct P)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
