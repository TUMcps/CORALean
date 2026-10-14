module

public import CORALean.ContSet.Conversion.Float.ZonoBundle_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Zonotope_to_Interval

@[expose] public section

/-!
# A bundle's box, at one component, over a floating-point scalar — the construction

`ZonoBundle.interval` is the construction; `ZonoBundle_to_Interval` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.interval (zB : ZonoBundle (Vec 𝕋 n)) (i : Fin zB.k) : Interval (Vec 𝕋 n) :=
  (zB.zonotope i).interval

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
