import CORALean.ContSet.Capsule.Float.Capsule
import CORALean.ContSet.Capsule.Real.Instances

/-!
# A float capsule is convex

What it denotes is the exact capsule's set, so the exact theorem applies.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.convex_construct (C : Capsule 𝕋 n) : Convex ℝ C.construct :=
  CORALean.Real.Capsule.convex_construct C.nominal

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
