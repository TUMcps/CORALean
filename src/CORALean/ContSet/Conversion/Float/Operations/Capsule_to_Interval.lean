module

public import CORALean.ContSet.Capsule.Float.Capsule
public import CORALean.ContSet.Capsule.Real.Instances
public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.ContSet.Conversion.Real.Capsule_to_Interval

@[expose] public section

/-!
# A capsule as a box, over a floating-point scalar — the construction

`Capsule.interval` is the construction; `Capsule_to_Interval` states and proves what it guarantees.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The box, each end rounded away from the capsule. -/
def Capsule.interval (C : Capsule 𝕋 n) : Interval (Vec 𝕋 n) where
  inf := fun i => subDown (C.c i) (addUp (absolute (C.g i)) C.r)
  sup := fun i => addUp (C.c i) (addUp (absolute (C.g i)) C.r)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
