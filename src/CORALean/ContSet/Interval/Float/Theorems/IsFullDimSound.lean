import CORALean.ContSet.Interval.Float.Operations.IsFullDim
import CORALean.ContSet.Interval.Float.Instances
import CORALean.ContSet.Interval.Real.Theorems.IsFullDimIff

/-!
# `Interval.isFullDim` is sound

A `true` answer is a strict inequality for every coordinate, `toReal_lt_of_ltStrict`, which is the
real characterisation `CORALean.Real.Interval.isFullDim_iff`.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


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
