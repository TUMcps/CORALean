import CORALean.ContSet.Polygon.Float.Operations.PieceSubset
import CORALean.ContSet.Polygon.Float.Polygon

/-!
# `Polygon.isConvex`, over a floating-point scalar

A sufficient test for a convex region: no piece at all, or one piece that holds every piece
(`Polygon.pieceSubset`, the vertex triangles and boxes certified), so the region is that one
convex piece. Only `true` is certain; a convex region split into several pieces none of which
holds the others answers `false`. CORA's comparison of boundary vertex counts (R-PG) is not
what is tested.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def Polygon.isConvex (P : Polygon 𝕋) : Bool :=
  P.sets.isEmpty || P.sets.any fun p => P.sets.all fun q => Polygon.pieceSubset q p

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
