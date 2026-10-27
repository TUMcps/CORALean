module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Interval.Real.Theorems.PlusExact
public import Mathlib.Order.BourbakiWitt

@[expose] public section

/-!
# `Interval.plus` contains the Minkowski sum

Nothing about sums of sets appears here — `Real` has already proved that. The
whole obligation is that each bound rounded the right way.

With `MulBetweenCorners` and the float intrinsics' outer theorems, this is the admissible
interval arithmetic [1, Def. 5] assumes, eq. (3.1) for `⊕`, proved here from directed rounding.

## Inputs
* `I₁` – first interval box
* `I₂` – second interval box

## Hypotheses
* none

## Conclusion
* the Minkowski sum of the two sets lies in the result box

## References

* [1] [K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion Methods".
      International Journal of Pure and Applied Mathematics,
      2003.](../../../../../../references/2003/makino-ijpam-taylor-models.md)
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

private theorem Interval.aux_plus_outer_refines (I₁ I₂ : Interval (Vec 𝕋 n)) :
    (I₁.nominal.plus I₂.nominal).construct ⊆ (I₁.plus I₂).construct := by
  intro x hx i
  exact ⟨le_trans (addDown_le_add _ _) (hx i).1, le_trans (hx i).2 (add_le_addUp _ _)⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.plus_outer (I₁ I₂ : Interval (Vec 𝕋 n)) :
    I₁.construct + I₂.construct ⊆ (I₁.plus I₂).construct :=
  subset_trans (Real.Interval.plus_outer I₁.nominal I₂.nominal)
    (Interval.aux_plus_outer_refines I₁ I₂)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
