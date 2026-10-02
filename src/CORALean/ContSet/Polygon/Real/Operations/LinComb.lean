import CORALean.ContSet.Polygon.Real.Polygon

/-!
# `Polygon.linComb`

CORA's `polygon/linComb`: the hull of every pair of pieces, one from each operand, as CORA's
`convHull(list1{i}, list2{j})` after triangulating.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The convex combinations of every pair of pieces, one from each polygon. -/
def Polygon.linComb (P Q : Polygon) : Polygon :=
  ⟨(P.sets ×ˢ Q.sets).map fun pq => VPolytope.linComb pq.1 pq.2⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
