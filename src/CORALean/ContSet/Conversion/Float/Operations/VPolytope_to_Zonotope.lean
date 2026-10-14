module

public import CORALean.ContSet.Conversion.Float.VPolytope_to_Interval
public import CORALean.ContSet.Conversion.Float.Interval_to_Zonotope

@[expose] public section

/-!
# A hull as a zonotope, over a floating-point scalar — the construction

`VPolytope.zonotope` is the construction; `VPolytope_to_Zonotope` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def VPolytope.zonotope (P : VPolytope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  P.interval.zonotope

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
