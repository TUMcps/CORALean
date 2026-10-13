import CORALean.ContSet.Interval.Float.Operations.Min
import CORALean.ContSet.Interval.Real.Theorems.MinExact

/-!
# `Interval.min` is exactly the set of entrywise minima

Nothing is rounded, so the stored box reads as exactly the exact layer's `min` of the readings, and
`Real.Interval.min_exact` carries over, under the same nonemptiness of the readings.
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

theorem Interval.min_exact {I₁ I₂ : Interval (Vec 𝕋 n)} (h₁ : I₁.nominal.IsNonempty)
    (h₂ : I₂.nominal.IsNonempty) :
    (I₁.min I₂).construct = Set.image2 (fun x y : Vec ℝ n => fun i => Min.min (x i) (y i))
      I₁.construct I₂.construct := by -- --- PROOF ---
  have h : (I₁.min I₂).nominal = I₁.nominal.min I₂.nominal := by
    unfold Interval.nominal Interval.min Real.Interval.min
    congr 1 <;> funext i <;> exact toReal_minimum _ _
  show (I₁.min I₂).nominal.construct = _
  rw [h]
  exact Real.Interval.min_exact h₁ h₂

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
