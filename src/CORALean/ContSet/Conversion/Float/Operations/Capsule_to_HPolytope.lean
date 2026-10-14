module

public import CORALean.ContSet.Conversion.Float.Capsule_to_Interval
public import CORALean.ContSet.Conversion.Float.Interval_to_HPolytope

@[expose] public section

/-!
# A capsule as a halfspace polytope, over a floating-point scalar — the construction

`Capsule.hPolytope` is the construction; `Capsule_to_HPolytope` states and proves what it
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

def Capsule.hPolytope (C : Capsule 𝕋 n) : HPolytope 𝕋 (Vec 𝕋 n) :=
  C.interval.hPolytope

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
