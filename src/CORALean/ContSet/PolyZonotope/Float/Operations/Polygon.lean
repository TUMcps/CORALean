import CORALean.ContSet.PolyZonotope.Float.Operations.PolygonPieces
import CORALean.ContSet.Conversion.Float.PolyZonotope_to_Zonotope
import CORALean.ContSet.Zonotope.Float.Operations.Polygon
import CORALean.ContSet.Polygon.Float.Operations.OfPieces

/-!
# `PolyZonotope.polygon`, over a floating-point scalar

CORA's `polygon(pZ, splits)` for a two-dimensional polynomial zonotope: the union of the polygons of
the zonotopes of the pieces after `splits` rounds of `splitLongestGen`. The zonotope of a piece
is `PolyZonotope.zonotope` (every monomial a free factor in `[-1, 1]`), a wider enclosure than
CORA's `zonotope(pZ)`, which halves the all-even columns; its polygon is the float
`Zonotope.polygon` (the sorted walk, `2 h` vertices). The choice of the pieces to refine is the
parameter `pick`, as at the real layer.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The union of the polygons of the zonotopes of the final pieces. -/
def PolyZonotope.polygon (pZ : PolyZonotope (Vec 𝕋 2)) (splits : ℕ)
    (pick : ℕ → PolyZonotope (Vec 𝕋 2) → Bool) : Polygon 𝕋 :=
  Polygon.ofPieces ((pZ.polygonPieces splits pick).map fun q => q.zonotope.polygon)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
