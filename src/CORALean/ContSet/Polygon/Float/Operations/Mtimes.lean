module

public import CORALean.ContSet.Polygon.Float.Polygon
public import CORALean.ContSet.VPolytope.Float.Operations.Mtimes

@[expose] public section

/-!
# `Polygon.mtimes`, over a floating-point scalar

Every piece mapped by the float matrix.
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

/-- Every piece mapped by `M`. -/
def Polygon.mtimes (M : Mat 𝕋 2 2) (P : Polygon 𝕋) : Polygon 𝕋 :=
  ⟨P.sets.map fun p => (VPolytope.mtimes M p).materialise⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
