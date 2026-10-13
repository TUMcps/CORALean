import CORALean.ContSet.SpectraShadow.Real.SpectraShadow
import CORALean.ContSet.SpectraShadow.Real.Theorems.Convex
import Mathlib.Analysis.Convex.Hull

/-!
# `SpectraShadow.contains_iff_vertices`

CORA's `'exact'` branch of `contains_` for a set operand `T` (a zonotope, interval, polytope,
conZonotope or zonoBundle): the point test on each of its `vertices`. A convex hull of points lies
in a spectrahedral shadow exactly when the points do, since the shadow is convex.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.contains_iff_vertices (S : SpectraShadow α) (T V : Set α)
    (hT : convexHull ℝ V = T) : T ⊆ S.construct ↔ V ⊆ S.construct := by
  subst hT
  exact ⟨fun h => (subset_convexHull ℝ V).trans h,
    fun h => convexHull_min h S.convex_construct⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
