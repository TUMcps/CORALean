module

public import CORALean.ContSet.Conversion.Float.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Zonotope_to_ZonoBundle

@[expose] public section

/-!
# A box as a bundle of one, over a floating-point scalar — the construction

`Interval.zonoBundle` is the construction; `Interval_to_ZonoBundle` states and proves what it
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

def Interval.zonoBundle (I : Interval (Vec 𝕋 n)) : ZonoBundle (Vec 𝕋 n) := I.zonotope.zonoBundle

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
