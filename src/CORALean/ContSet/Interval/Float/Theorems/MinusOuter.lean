import CORALean.ContSet.Interval.Float.Operations.Minus
import CORALean.ContSet.Interval.Real.Operations.Minus
import CORALean.ContSet.Interval.Real.Theorems.MinusOuter
import Mathlib.Order.BourbakiWitt

/-!
# `Interval.minus` contains the pointwise difference of the sets

Nothing about differences of sets appears here: `Real` has already proved that. The whole
obligation is that each bound rounded the right way.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem Interval.aux_minus_outer_refines (I₁ I₂ : Interval (Vec 𝕋 n)) :
    (I₁.nominal.minus I₂.nominal).construct ⊆ (I₁.minus I₂).construct := by
  intro x hx i
  exact ⟨le_trans (subDown_le_sub _ _) (hx i).1, le_trans (hx i).2 (sub_le_subUp _ _)⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.minus_outer (I₁ I₂ : Interval (Vec 𝕋 n)) :
    I₁.construct - I₂.construct ⊆ (I₁.minus I₂).construct :=
  subset_trans (Real.Interval.minus_outer I₁.nominal I₂.nominal)
    (Interval.aux_minus_outer_refines I₁ I₂)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
