import CORALean.ContSet.Polygon.Float.Operations.PieceSubset
import CORALean.ContSet.Polygon.Float.Polygon

/-!
# `Polygon.subtract`, over a floating-point scalar

The regularized difference of two polygons as a polygon again, by dropping every piece of the
minuend that one piece of the subtrahend certainly covers (`Polygon.pieceSubset`, sufficient
only). What is left are whole pieces: a piece only partly covered is kept entire, so the
result is an outer approximation, coarser than the real region `closure (interior P₁ \ P₂)`
by the covered part of each kept piece. Cutting a piece along the facets of the subtrahend
needs the facets of a float vertex description rounded inward, which the float layer does not
have (`VPolytope.hPolytope` rounds outward at given directions, and `HPolytope.not` is inner).
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The pieces of `P` that no single piece of `Q` certainly covers. -/
def Polygon.subtract (P Q : Polygon 𝕋) : Polygon 𝕋 :=
  ⟨P.sets.filter fun p => !(Q.sets.any fun q => Polygon.pieceSubset p q)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
