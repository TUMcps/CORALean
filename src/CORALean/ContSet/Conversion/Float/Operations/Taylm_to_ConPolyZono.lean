module

public import CORALean.ContSet.Conversion.Float.PolyZonotope_to_ConPolyZono
public import CORALean.ContSet.Conversion.Float.Taylm_to_PolyZonotope

@[expose] public section

/-!
# An array of Taylor models as a constrained polynomial zonotope, over a floating-point scalar

`Taylm.conPolyZono` is the construction; `Taylm_to_ConPolyZono` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.conPolyZono (T : Fin m → Taylm 𝕋 n) : ConPolyZono 𝕋 (Vec 𝕋 m) :=
  (Taylm.polyZonotope T).conPolyZono

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
