module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Real.Theorems.MaxExact

@[expose] public section

/-!
# `Interval.max` is exactly the set of entrywise maxima

Nothing is rounded, so the stored box reads as exactly the exact layer's `max` of the readings, and
`Real.Interval.max_exact` carries over, under the same nonemptiness of the readings.
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

theorem Interval.max_exact {I₁ I₂ : Interval (Vec 𝕋 n)} (h₁ : I₁.nominal.IsNonempty)
    (h₂ : I₂.nominal.IsNonempty) :
    (I₁.max I₂).construct = Set.image2 (fun x y : Vec ℝ n => fun i => Max.max (x i) (y i))
      I₁.construct I₂.construct := by -- --- PROOF ---
  have h : (I₁.max I₂).nominal = I₁.nominal.max I₂.nominal := by
    unfold Interval.nominal Interval.max Real.Interval.max
    congr 1 <;> funext i <;> exact toReal_maximum _ _
  show (I₁.max I₂).nominal.construct = _
  rw [h]
  exact Real.Interval.max_exact h₁ h₂

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
