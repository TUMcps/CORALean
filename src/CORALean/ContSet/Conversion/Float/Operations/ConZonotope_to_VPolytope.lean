module

public import CORALean.ContSet.Conversion.Float.ConZonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Interval_to_VPolytope

@[expose] public section

/-!
# A constrained zonotope as vertices, over a floating-point scalar — the construction

`ConZonotope.vPolytopeBox` is the construction; `ConZonotope_to_VPolytope` states and proves what it
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

def ConZonotope.vPolytopeBox (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : VPolytope (Vec 𝕋 n) :=
  Interval.vPolytope cZ.interval

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
