import CORALean.ContSet.Interval.Float.Operations.Isequal
import CORALean.ContSet.Interval.Float.Theorems.LeSound

/-!
# `Interval.isequal` is sound

A `true` answer is `le` each way, which is the exact layer's `le_subset` each way, so the two boxes
denote the same set. `false` refutes nothing, as `le` is certified in one direction only.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.isequal_sound {I J : Interval (Vec 𝕋 n)} (h : Interval.isequal I J = true) :
    I.construct = J.construct := by
  rw [Interval.isequal, Bool.and_eq_true] at h
  exact Set.Subset.antisymm (Interval.le_subset h.1) (Interval.le_subset h.2)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
