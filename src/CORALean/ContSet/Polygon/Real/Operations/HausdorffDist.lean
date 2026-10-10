import CORALean.ContSet.Polygon.Real.Polygon
import CORALean.Global.EuclideanNorm

/-!
# `Polygon.hausdorffDist`

CORA's `polygon/hausdorffDist(pgon, S)` for a numeric `S`, the columns of a matrix of points: for
each point `0` if the polygon contains it, else its Euclidean distance to the boundary segments
(`aux_distPolygonPoint`), and the largest of these, starting from `val = 0`. The region's boundary
is `frontier`, which the segments of a single boundary loop cover; the loop's `NaN` separators
(several regions, holes) are not modelled. The distance is taken in the Euclidean norm, through
`toEuclidean`, as `Vec` carries the supremum norm. The polygon–polygon branch reads vertices of
boundary loops (R-PG) and is not defined here. The value is the largest distance from a point
to the polygon, one direction of the Hausdorff distance, not both (FINDINGS.md).
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

open Classical in
/-- The largest distance from a point of `S` to the polygon. -/
noncomputable def Polygon.hausdorffDist (P : Polygon) (S : List (Vec ℝ 2)) : ℝ :=
  let R : Set (Vec ℝ 2) := ContSet.construct P
  -- `val_ = 0` if `contains(pgon, S(:,i))`, else the distance to the boundary segments
  let val_ : Vec ℝ 2 → ℝ := fun s =>
    if s ∈ R then 0 else Metric.infDist (toEuclidean s) (toEuclidean '' frontier R)
  -- `val = 0; for i = 1:size(S,2): val = max(val, val_)`
  (S.map val_).foldl max 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
