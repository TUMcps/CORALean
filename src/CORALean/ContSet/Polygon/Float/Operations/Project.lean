import CORALean.ContSet.Polygon.Float.Polygon

/-!
# `Polygon.project`, over a floating-point scalar

Every piece read at the coordinates `dims`; also `projectHighDim_` and `lift_` at `N = 2`.
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

/-- Every piece read at the coordinates `dims`. -/
def Polygon.project (P : Polygon 𝕋) (dims : Fin 2 → Fin 2) : Polygon 𝕋 :=
  ⟨P.sets.map fun p => VPolytope.project p dims⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
