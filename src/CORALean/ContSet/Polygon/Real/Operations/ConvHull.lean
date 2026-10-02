import CORALean.ContSet.Polygon.Real.Operations.Vertices

/-!
# `Polygon.convHull`

CORA's `polygon/convHull_` at one polygon, and with it `polytope(pgon)`, which is
`polytope(vertices(convHull(pgon)))`: the polytope spanned by all vertices.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The polytope spanned by the vertices of all pieces. -/
def Polygon.convHull (P : Polygon) : VPolytope (Vec ℝ 2) :=
  ⟨P.vertices.length, fun i => P.vertices.get i⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
