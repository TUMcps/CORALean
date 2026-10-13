module

public import CORALean.ContSet.Polygon.Real.Polygon
public import CORALean.ContSet.VPolytope.Real.Instances
public import CORALean.ContSet.SetUnion.Operations.Plus

@[expose] public section

/-!
# `Polygon.plus`

CORA's `polygon/plus` at a polygon: every piece of one added to every piece of the other, which
is what CORA does after triangulating both (the sum of two convex pieces is the hull of the
vertex sums). `SetUnion.plus` at `VPolytope.plus`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The Minkowski sum: every pair of pieces, summed. -/
def Polygon.plus (P Q : Polygon) : Polygon := SetUnion.plus P Q

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
