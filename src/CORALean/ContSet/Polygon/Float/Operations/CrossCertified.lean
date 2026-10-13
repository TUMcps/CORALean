import CORALean.ContSet.Polygon.Float.Operations.OrientBounds
import CORALean.ContSet.Polygon.Float.Polygon

/-!
# `Polygon.crossCertified`

Three vertices of a float piece are certainly not collinear: the cross product
`(b - a) × (c - a)`, bracketed by `Polygon.orientBounds`, is certified on one side of `0` by
`ltStrict`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The cross product of `(b - a, c - a)`, certified on one side of zero. -/
def Polygon.crossCertified (p : VPolytope (Vec 𝕋 2)) (a b c : Fin p.k) : Bool :=
  let D := Polygon.orientBounds (p.V a) (p.V b) (p.V c)
  ltStrict zero D.1 || ltStrict D.2 zero

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
