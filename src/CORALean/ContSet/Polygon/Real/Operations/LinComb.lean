module

public import CORALean.ContSet.Polygon.Real.Polygon
public import CORALean.ContSet.VPolytope.Real.Operations.LinComb

@[expose] public section

/-!
# `Polygon.linComb`

CORA's `polygon/linComb`: the hull of every pair of pieces, one from each operand, as CORA's
`convHull(list1{i}, list2{j})` after triangulating.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The convex combinations of every pair of pieces, one from each polygon. -/
def Polygon.linComb (P Q : Polygon) : Polygon :=
  ⟨(P.sets ×ˢ Q.sets).map fun pq => VPolytope.linComb pq.1 pq.2⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
