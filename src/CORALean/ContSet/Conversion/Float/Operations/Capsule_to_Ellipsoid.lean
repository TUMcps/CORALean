module

public import CORALean.ContSet.Conversion.Float.Capsule_to_Interval
public import CORALean.ContSet.Conversion.Float.Interval_to_Ellipsoid

@[expose] public section

/-!
# A capsule as an ellipsoid, over a floating-point scalar — the construction

`Capsule.ellipsoid` is the construction; `Capsule_to_Ellipsoid` states and proves what it
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

/-- The scaling `σ` is the one `Interval.ellipsoid` asks for: a float at least `√n`. -/
def Capsule.ellipsoid (C : Capsule 𝕋 n) (σ : 𝕋) : Ellipsoid 𝕋 n :=
  C.interval.ellipsoid σ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
