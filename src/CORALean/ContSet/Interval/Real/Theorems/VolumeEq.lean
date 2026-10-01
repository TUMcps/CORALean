import CORALean.ContSet.Interval.Real.Operations.Volume
import CORALean.ContSet.Interval.Real.Instances

/-!
# `Interval.volume` is the Lebesgue volume

The box is `Set.Icc inf sup`, whose volume Mathlib gives as the product of the widths. A crossed
box is empty and so is the product's zero factor: no separate case.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.volume_eq (I : Interval (Vec ℝ n)) :
    MeasureTheory.volume (construct I) = I.volume := by -- --- PROOF ---
  have hc : construct I = Set.Icc I.inf I.sup := by
    ext x
    exact ⟨fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩, fun h i => ⟨h.1 i, h.2 i⟩⟩
  rw [hc]
  exact Real.volume_Icc_pi

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
