module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.ContSet.Interval.Float.Operations.MinkDiff
public import CORALean.ContSet.Interval.Real.Operations.MinkDiff
public import CORALean.ContSet.Interval.Real.Theorems.MinkDiffInner

@[expose] public section

/-!
# `Interval.minkDiff` is an inner approximation of the Minkowski difference

Nothing about the Minkowski difference itself appears here — `Real` has already
proved it. The whole obligation is that each bound rounded the right way:
`subUp` on the lower bound and `subDown` on the upper only shrink the box that
`nominal.minkDiff` would give, so the float result stays inside it.

## Inputs
* `I₁` – first interval box
* `I₂` – second interval box

## Hypotheses
* none

## Conclusion
* the float difference box lies inside the Minkowski difference
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

private theorem Interval.aux_minkDiff_inner_refines (I₁ I₂ : Interval (Vec 𝕋 n)) :
    (I₁.minkDiff I₂).construct ⊆ (I₁.nominal.minkDiff I₂.nominal).construct := by
  intro x hx i
  exact ⟨le_trans (sub_le_subUp _ _) (hx i).1, le_trans (hx i).2 (subDown_le_sub _ _)⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.minkDiff_inner (I₁ I₂ : Interval (Vec 𝕋 n)) :
    (I₁.minkDiff I₂).construct ⊆ minkowskiDiff I₁.construct I₂.construct :=
  subset_trans (Interval.aux_minkDiff_inner_refines I₁ I₂)
    (Real.Interval.minkDiff_inner I₁.nominal I₂.nominal)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
