import CORALean.ContSet.ContSet.Theorems.SegmentsEqConvexJoin

/-!
# For two convex nonempty sets the segments are the convex hull of the union

`convexHull_union` and `convexJoin`: the hull of a union is the join of the hulls, and a convex
set is its own hull. So where `LinComb` encloses the segments, a convex operand pair gets the convex
hull of the union enclosed, which is what CORA's `convHull_` asks for.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem convexHull_union_eq_segments {X Y : Set α} (hX : X.Nonempty) (hY : Y.Nonempty)
    (cX : Convex ℝ X) (cY : Convex ℝ Y) :
    convexHull ℝ (X ∪ Y) = segments X Y := by
  rw [convexHull_union hX hY, convexHull_eq_self.2 cX, convexHull_eq_self.2 cY,
    segments_eq_convexJoin]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
