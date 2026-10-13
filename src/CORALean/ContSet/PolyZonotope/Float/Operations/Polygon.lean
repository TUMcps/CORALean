module

public import CORALean.ContSet.PolyZonotope.Float.Operations.PolygonPieces
public import CORALean.ContSet.Conversion.Float.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Zonotope.Float.Operations.Polygon
public import CORALean.ContSet.Polygon.Float.Operations.OfPieces

@[expose] public section

/-!
# `PolyZonotope.polygon`, over a floating-point scalar

CORA's `polygon(pZ, splits)` for a two-dimensional polynomial zonotope: the union of the polygons of
the zonotopes of the pieces after `splits` rounds of `splitLongestGen`. The zonotope of a piece
is `PolyZonotope.zonotope` (every monomial a free factor in `[-1, 1]`), a wider enclosure than
CORA's `zonotope(pZ)`, which halves the all-even columns; its polygon is the float
`Zonotope.polygon` (the sorted walk, `2 h` vertices). The choice of the pieces to refine is the
parameter `pick`, as at the real layer.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


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
