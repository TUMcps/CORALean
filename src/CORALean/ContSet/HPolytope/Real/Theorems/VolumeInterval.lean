module

public import CORALean.ContSet.HPolytope.Real.Operations.Volume
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalHPolytopeExact
public import CORALean.ContSet.Interval.Real.Theorems.VolumeEq
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_HPolytope

@[expose] public section

/-!
# The volume of a box's halfspace form

The H-representation of a box (`Interval.hPolytope`) denotes the box (`hPolytope_exact`), so its
volume is the product of the widths, `Interval.volume`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.volume_hPolytope_interval (I : Interval (Vec ℝ n)) :
    I.hPolytope.volume = I.volume := by
  unfold HPolytope.volume
  rw [Interval.hPolytope_exact]
  exact Interval.volume_eq I


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
