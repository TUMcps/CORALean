module

public import CORALean.ContSet.Polygon.Real.Polygon
public import Mathlib.LinearAlgebra.AffineSpace.Combination

@[expose] public section

/-!
# `Polygon.isFullDim`

CORA's `polygon/isFullDim` counts the boundary vertices of the polyshape (`size(V,2) > 2`). On the
region given as convex pieces the question is whether the region has an interior point, which
holds iff some piece has vertices that affinely span the plane (`Polygon.isFullDim_iff`). The
boundary-vertex count itself (R-PG) is not formalized.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Some piece has vertices that affinely span the plane. -/
def Polygon.isFullDim (P : Polygon) : Prop :=
  ∃ p ∈ P.sets, affineSpan ℝ (Set.range p.V) = ⊤

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
