module

public import CORALean.ContSet.Polygon.Float.Operations.OrientBounds

@[expose] public section

/-!
# `Polygon.inTriangle`

A point lies in the triangle `a b c`: the triangle's orientation is certified positive by
`ltStrict`, and the three orientations of the point against its edges (`b c x`, `c a x`,
`a b x`) are certified nonnegative by `le`. These are the barycentric coordinates times the
triangle's orientation, so `true` is certain; a triangle of the other orientation is the same
triangle with two corners swapped, which a search over corners also tries.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def Polygon.inTriangle (a b c x : Vec 𝕋 2) : Bool :=
  ltStrict zero (Polygon.orientBounds a b c).inf &&
    le zero (Polygon.orientBounds b c x).inf && le zero (Polygon.orientBounds c a x).inf &&
      le zero (Polygon.orientBounds a b x).inf

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
