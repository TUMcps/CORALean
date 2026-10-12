import CORALean.ContSet.Polygon.Float.Operations.Subtract

/-!
# `Polygon.mldivide`, over a floating-point scalar

CORA's `polygon/mldivide(pgon, S)` subtracts the converted operand `polygon(S)`: it is
`Polygon.subtract` at the converted float polygon, which the caller supplies (the conversions
are the rows of the other classes).
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

/-- The difference with the polygon `Sp` standing for the second operand. -/
def Polygon.mldivide (P Sp : Polygon 𝕋) : Polygon 𝕋 := Polygon.subtract P Sp

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
