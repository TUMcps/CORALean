module

public import CORALean.ContSet.Interval.Float.Operations.Abs
public import CORALean.ContSet.Interval.Real.Theorems.AbsExact

@[expose] public section

/-!
# `Interval.abs` is exactly the image under the absolute value

Nothing is rounded, so the stored box reads as the exact layer's `abs` of the readings.
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

theorem Interval.abs_exact (I : Interval (Vec 𝕋 n)) :
    (I.abs).construct = (fun x i => |x i|) '' I.construct := by -- --- PROOF ---
  have h : I.abs.nominal = I.nominal.abs := by
    unfold Interval.nominal Interval.abs Real.Interval.abs
    congr 1
    · funext i
      show toReal (maximum zero (maximum (I.inf i) (neg (I.sup i)))) = _
      simp only [toReal_maximum, toReal_zero, toReal_neg]
      rfl
    · funext i
      show toReal (maximum (neg (I.inf i)) (I.sup i)) = _
      simp only [toReal_maximum, toReal_neg]
      rfl
  show I.abs.nominal.construct = _
  rw [h]
  exact Real.Interval.abs_exact I.nominal


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
