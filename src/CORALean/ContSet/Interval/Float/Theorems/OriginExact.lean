import CORALean.ContSet.Interval.Float.Operations.Origin
import CORALean.ContSet.Interval.Real.Theorems.OriginExact

/-!
# `Interval.origin` is exactly the origin

`zero` reads as `0`, so the stored box denotes the exact layer's origin interval.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.origin_exact (n : ℕ) :
    (Interval.origin n : Interval (Vec 𝕋 n)).construct = {0} := by -- --- PROOF ---
  have h : (Interval.origin n : Interval (Vec 𝕋 n)).nominal = Real.Interval.origin n := by
    unfold Interval.nominal Interval.origin Real.Interval.origin Real.Interval.point
    congr 1 <;> funext i <;> exact toReal_zero
  show (Interval.origin n : Interval (Vec 𝕋 n)).nominal.construct = {0}
  rw [h]
  exact Real.Interval.origin_exact n

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
