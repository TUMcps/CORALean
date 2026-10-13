module

public import CORALean.ContSet.VPolytope.Real.Theorems.Convex
public import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases

@[expose] public section

/-!
# A vertex polytope is full-dimensional iff its vertices affinely span

CORA's `isFullDim` for a polytope in vertex representation (`priv_isFullDim_V`). The polytope is
the convex hull of its vertices, and a convex set has an interior point iff its affine span is the
whole space; the affine span of a hull is that of the vertices. Stated at `construct`, which is
what `ContSet.IsFullDim` unfolds to, over any finite-dimensional real normed space. No vertices
means the empty set, whose span is `⊥`, never `⊤`. The half-space representation needs the
implied-equality test, which this does not claim.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Set

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α] [FiniteDimensional ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.isFullDim_iff (P : VPolytope α) :
    (interior P.construct).Nonempty ↔ affineSpan ℝ (range P.V) = ⊤ := by
  rw [P.convex_construct.interior_nonempty_iff_affineSpan_eq_top, P.construct_eq_convexHull,
    affineSpan_convexHull]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
