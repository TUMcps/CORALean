module

public import CORALean.ContSet.Interval.Float.Operations.IsFullDim
public import CORALean.ContSet.Interval.Float.Instances
public import CORALean.ContSet.Interval.Real.Theorems.IsFullDimIff

@[expose] public section

/-!
# `Interval.isFullDim` is sound

A `true` answer is a strict inequality for every coordinate, `toReal_lt_of_ltStrict`, which is the
real characterisation `CORALean.Real.Interval.isFullDim_iff`.

## Inputs
* `I` – interval box

## Hypotheses
* `h` – test returned true

## Conclusion
* the box is full-dimensional
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic ContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.isFullDim_sound {I : Interval (Vec 𝕋 n)} (h : Interval.isFullDim I = true) :
    ContSet.IsFullDim I := by
  simp only [Interval.isFullDim, List.all_eq_true, List.mem_finRange, forall_const] at h
  exact (CORALean.Real.Interval.isFullDim_iff I.nominal).2 fun j => toReal_lt_of_ltStrict (h j)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
