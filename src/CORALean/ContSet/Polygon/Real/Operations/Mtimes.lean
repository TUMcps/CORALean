import CORALean.ContSet.Polygon.Real.Polygon
import CORALean.ContSet.VPolytope.Real.Operations.Mtimes

/-!
# `Polygon.mtimes`

CORA's `polygon/mtimes` at a `2 × 2` matrix: every piece mapped by it. CORA maps the vertices of
the polyshape.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every piece mapped by `M`. -/
def Polygon.mtimes (M : Mat ℝ 2 2) (P : Polygon) : Polygon :=
  ⟨P.sets.map (VPolytope.mtimes M)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
