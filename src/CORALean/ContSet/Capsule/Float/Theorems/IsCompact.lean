import CORALean.ContSet.Capsule.Float.Capsule
import CORALean.ContSet.Capsule.Real.Instances

/-!
# A float capsule is compact

What it denotes is the exact capsule's set, so the exact theorem applies.
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

theorem Capsule.isCompact_construct (C : Capsule 𝕋 n) : IsCompact C.construct :=
  CORALean.Real.Capsule.isCompact_construct C.nominal

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
