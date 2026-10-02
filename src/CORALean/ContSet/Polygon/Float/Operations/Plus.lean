import CORALean.ContSet.Polygon.Float.Polygon

/-!
# `Polygon.plus`, over a floating-point scalar

Every pair of pieces summed by the float polytope's own `plus`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every pair of pieces, summed. -/
def Polygon.plus (P Q : Polygon 𝕋) : Polygon 𝕋 := SetUnion.plus P Q

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
