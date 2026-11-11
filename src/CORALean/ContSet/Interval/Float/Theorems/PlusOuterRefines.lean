module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Real.Operations.Basic

@[expose] public section

/-!
# The float `Interval.plus` refines the real one

The real sum of the two intervals' real readings (`toReal`) lies in the float sum: the
lower bound is rounded down and the upper bound up, so each coordinate of the real sum
is bracketed. This is the whole float obligation of `Interval.plus_outer`.

## Inputs
* `I₁` – first interval box
* `I₂` – second interval box

## Hypotheses
* none

## Conclusion
* the real sum of the real readings lies in the float sum
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   11-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

-- each bound is rounded outward, so it brackets the exact bound of the real sum
theorem Interval.plus_outer_refines (I₁ I₂ : Interval (Vec 𝕋 n)) :
    (I₁.toReal.plus I₂.toReal).toSet ⊆ (I₁.plus I₂).toSet := by
  intro x hx i
  exact ⟨le_trans (addDown_le_add _ _) (hx i).1, le_trans (hx i).2 (add_le_addUp _ _)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
