import CORALean.ContSet.Capsule.Float.Capsule
import CORALean.ContSet.Capsule.Real.Instances

/-!
# The stored centre of a float capsule

It is in the capsule exactly when the stored radius is non-negative.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.centre_mem_construct_iff (C : Capsule 𝕋 n) :
    toRealVec C.c ∈ C.construct ↔ 0 ≤ toReal C.r :=
  CORALean.Real.Capsule.centre_mem_construct_iff C.nominal

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
