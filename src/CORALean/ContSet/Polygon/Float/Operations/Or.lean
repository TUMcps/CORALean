module

public import CORALean.ContSet.Polygon.Float.Polygon

@[expose] public section

/-!
# `Polygon.or`, over a floating-point scalar

The pieces of both; nothing is computed.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The union: the pieces of both. -/
def Polygon.or (P Q : Polygon 𝕋) : Polygon 𝕋 := ⟨P.sets ++ Q.sets⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
