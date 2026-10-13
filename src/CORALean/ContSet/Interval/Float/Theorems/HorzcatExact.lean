import CORALean.ContSet.Interval.Float.Operations.Horzcat
import CORALean.ContSet.Interval.Real.Theorems.HorzcatExact

/-!
# `Interval.horzcat` over floats is exact

Concatenation commutes with reading the floats as reals, so the stored box denotes the exact
layer's concatenation of the readings.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n₁ n₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.horzcat_exact (I : Interval (Mat 𝕋 m n₁)) (J : Interval (Mat 𝕋 m n₂)) :
    (I.horzcat J).construct =
      (fun p : Mat ℝ m n₁ × Mat ℝ m n₂ => fun i => Fin.append (p.1 i) (p.2 i)) ''
        (I.construct ×ˢ J.construct) := by -- --- PROOF ---
  have h : (I.horzcat J).nominal = Real.Interval.horzcat I.nominal J.nominal := by
    unfold Interval.nominal Interval.horzcat Real.Interval.horzcat
    congr 1 <;> funext i k <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) k <;>
      simp [RealImage.realImage, toRealMat]
  show (I.horzcat J).nominal.construct = _
  rw [h]
  exact Real.Interval.horzcat_exact I.nominal J.nominal

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
