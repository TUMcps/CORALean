import CORALean.ContSet.Polygon.Float.Operations.OrientBounds
import CORALean.ContSet.Polygon.Float.Polygon

/-!
# `Polygon.crossCertified`

Three vertices of a float piece are certainly not collinear: the cross product
`(b - a) × (c - a)`, bracketed by `Polygon.orientBounds`, is certified on one side of `0` by
`ltStrict`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The cross product of `(b - a, c - a)`, certified on one side of zero. -/
def Polygon.crossCertified (p : VPolytope 𝕋 2) (a b c : Fin p.k) : Bool :=
  let D := Polygon.orientBounds (fun i => p.V i a) (fun i => p.V i b) (fun i => p.V i c)
  ltStrict zero D.1 || ltStrict D.2 zero

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
