module

public import CORALean.ContSet.Conversion.Float.Capsule_to_Interval
public import CORALean.ContSet.Conversion.Float.Interval_to_VPolytope

@[expose] public section

/-!
# A capsule as a vertex polytope, over a floating-point scalar — the construction

`Capsule.vPolytope` is the construction; `Capsule_to_VPolytope` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Capsule.vPolytope (C : Capsule 𝕋 n) : VPolytope (Vec 𝕋 n) :=
  C.interval.vPolytope

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
