import CORALean.ContDynamics.LinearSys.MatExp.Operations.HalfSqBoundsFloat
import CORALean.Global.Float.SoundFloatArithmetic

/-!
# `halfSqBounds` brackets `t² / 2`

`mulDown`/`mulUp` of `t` with itself bracket `t * t`, and `half` is exact.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.halfSqBounds_mem (t : 𝕋) :
    toReal (MatExp.halfSqBounds t).1 ≤ toReal t ^ 2 / 2
      ∧ toReal t ^ 2 / 2 ≤ toReal (MatExp.halfSqBounds t).2 := by
  have h1 := mulDown_le_mul t t
  have h2 := mul_le_mulUp t t
  simp only [MatExp.halfSqBounds, toReal_half]
  constructor <;> nlinarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
