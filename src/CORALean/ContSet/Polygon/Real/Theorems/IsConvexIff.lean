import CORALean.ContSet.Polygon.Real.Operations.IsConvex
import CORALean.ContSet.Polygon.Real.Theorems.ConvHullExact

/-!
# `Polygon.isConvex` is convexity of the region

Exactly, by `Polygon.convHull_exact`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.isConvex_iff (P : Polygon) :
    Polygon.isConvex P ↔ Convex ℝ (ContSet.construct P) := by -- --- PROOF ---
  unfold Polygon.isConvex
  rw [Polygon.convHull_exact]
  constructor
  · intro h
    have : convexHull ℝ (ContSet.construct P) = ContSet.construct P :=
      Set.Subset.antisymm h (subset_convexHull ℝ _)
    rw [← this]; exact convex_convexHull ℝ _
  · intro h
    exact (convexHull_min subset_rfl h)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
