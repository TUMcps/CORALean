import CORALean.ContSet.Interval.Real.Theorems.CenterSubRadius
import CORALean.ContSet.Interval.Real.Theorems.CenterAddRadius
import CORALean.ContSet.Interval.Real.Operations.IntervalMatrix

/-!
# `Interval.intervalMatrix` is the same box

The centre and half-width of a box give its bounds back, so `intervalMatrix(center(I), rad(I))` is
`I` itself, and denotes the same set, with no hypothesis.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [inst : Entrywise α ι]

include inst


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.intervalMatrix_eq (I : Interval α) : I.intervalMatrix = I := by -- --- PROOF ---
  cases I with
  | mk lo hi =>
    have h₁ := Interval.center_sub_radius (⟨lo, hi⟩ : Interval α)
    have h₂ := Interval.center_add_radius (⟨lo, hi⟩ : Interval α)
    unfold Interval.intervalMatrix Interval.ofCenterRadius
    rw [h₁, h₂]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
