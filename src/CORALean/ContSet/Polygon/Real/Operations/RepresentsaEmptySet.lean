import CORALean.ContSet.Polygon.Real.Polygon

/-!
# `Polygon.representsaEmptySet`

CORA's `polygon/representsa_` at `'emptySet'`: `isempty(vertices_(pgon))`. A polygon is empty
iff every piece has no vertices.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every piece has no vertex. -/
def Polygon.representsaEmptySet (P : Polygon) : Bool :=
  P.sets.all fun p => p.k == 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
