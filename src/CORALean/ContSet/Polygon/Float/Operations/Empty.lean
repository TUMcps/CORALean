import CORALean.ContSet.Polygon.Float.Polygon

/-!
# `Polygon.empty`, over a floating-point scalar

No pieces.
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

/-- The empty polygon. -/
def Polygon.empty (𝕋 : Type) [FloatOps 𝕋] : Polygon 𝕋 := ⟨[]⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
