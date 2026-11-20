module

public import CORALean.ContSet.Taylm.Float.Operations.Basic
public import CORALean.ContSet.Taylm.Float.Theorems.PlusMergedOuter
public import CORALean.ContSet.Taylm.Float.Theorems.UminusOuter

@[expose] public section

/-!
# `Taylm.minusMerged` encloses the difference

## Inputs
* `T₁` – first Taylor model
* `T₂` – second Taylor model
* `f` – function the first encloses
* `g` – function the second encloses

## Hypotheses
* `h₁` – `T₁` encloses `f`
* `h₂` – `T₂` encloses `g`

## Conclusion
* the difference model encloses `f - g`
-/

-- Authors:       Claude Opus 5.5
-- Written:       20-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.minusMerged_outer {T₁ T₂ : Taylm 𝕋 n} {f g : Vec ℝ n → ℝ} (h₁ : T₁.Encloses f)
    (h₂ : T₂.Encloses g) :
    (T₁.minusMerged T₂).Encloses fun t => f t - g t := by
  show (T₁.plusMerged T₂.uminus).Encloses _
  simpa only [sub_eq_add_neg] using Taylm.plusMerged_outer h₁ (Taylm.uminus_outer h₂)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
