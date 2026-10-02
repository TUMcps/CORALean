import CORALean.ContSet.Interval.Float.Operations.Or
import CORALean.ContSet.Interval.Real.Operations.Or
import CORALean.ContSet.Interval.Real.Theorems.OrOuter
import Mathlib.Order.BourbakiWitt

/-!
# `Interval.or` contains the union

Nothing is rounded, so the stored box reads as exactly the exact layer's `or` of the readings.
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

theorem Interval.aux_or_outer_refines (I₁ I₂ : Interval (Vec 𝕋 n)) :
    (I₁.nominal.or I₂.nominal).construct ⊆ (I₁.or I₂).construct := by -- --- PROOF ---
  intro x hx i
  refine ⟨?_, ?_⟩
  · show toReal (minimum _ _) ≤ x i
    rw [toReal_minimum]
    exact (hx i).1
  · show x i ≤ toReal (maximum _ _)
    rw [toReal_maximum]
    exact (hx i).2


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.or_outer (I₁ I₂ : Interval (Vec 𝕋 n)) :
    I₁.construct ∪ I₂.construct ⊆ (I₁.or I₂).construct :=
  subset_trans (Real.Interval.or_outer I₁.nominal I₂.nominal) (Interval.aux_or_outer_refines I₁ I₂)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
