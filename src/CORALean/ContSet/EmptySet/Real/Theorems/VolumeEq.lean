module

public import CORALean.ContSet.EmptySet.Real.Operations.Volume
public import CORALean.ContSet.EmptySet.Real.Instances

@[expose] public section

/-!
# `EmptySet.volume` is the Lebesgue volume

`0`, CORA's value, is the volume of `∅`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem EmptySet.volume_eq (E : EmptySet n) :
    MeasureTheory.volume (construct E) = E.volume := by
  change MeasureTheory.volume (∅ : Set (Vec ℝ n)) = 0
  exact MeasureTheory.measure_empty

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
