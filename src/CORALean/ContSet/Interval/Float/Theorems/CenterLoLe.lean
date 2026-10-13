import CORALean.ContSet.Interval.Float.Operations.CenterLo
import CORALean.ContSet.Interval.Real.Operations.Center

/-!
# `Interval.centerLo` is at most the real midpoint

The sum rounds down and `half` is exact.
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

theorem Interval.centerLo_le (I : Interval (Vec 𝕋 n)) (i : Fin n) :
    toReal (I.centerLo i) ≤ I.nominal.center i := by -- --- PROOF ---
  have h : I.nominal.center i = (toReal (I.inf i) + toReal (I.sup i)) / 2 := by
    show (2:ℝ)⁻¹ * (toReal (I.inf i) + toReal (I.sup i)) = _
    ring
  rw [h, Interval.centerLo, toReal_half]
  have := addDown_le_add (I.inf i) (I.sup i)
  linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
