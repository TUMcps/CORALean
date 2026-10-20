module

public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `Interval.le` is sound

A `true` answer chains `toReal_le_of_le` through every coordinate, which is the exact layer's
`le_subset` read at the stored bounds.

## Inputs
* `I` – first interval box
* `J` – second interval box

## Hypotheses
* `h` – test returned true

## Conclusion
* the first box is contained in the second
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

theorem Interval.le_subset {I J : Interval (Vec 𝕋 n)} (h : Interval.le I J = true) :
    I.construct ⊆ J.construct := by
  simp only [Interval.le, List.all_eq_true, List.mem_finRange, Bool.and_eq_true,
    forall_const] at h
  intro x hx j
  exact ⟨le_trans (toReal_le_of_le (h j).1) (hx j).1, le_trans (hx j).2 (toReal_le_of_le (h j).2)⟩


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
