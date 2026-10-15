module

public import CORALean.ContSet.Interval.Real.Operations.Basic

@[expose] public section

/-!
# `Interval.center_add_radius`

The center plus the half-width is the upper bound: the split `center ± radius` gives the box back.

[1, Sec. 2] writes an interval as `mid([x]) ⊕ rad([x]) ⊗ [-1, 1]`; this is its upper end.

## References

* [1] M. Althoff and D. Grebenyuk. "Implementation of Interval Arithmetic in CORA 2016". In
      Proc. of the 3rd International Workshop on Applied Verification for Continuous and Hybrid
      Systems (ARCH16), EPiC Series in Computing, vol. 43, pp. 91-105, 2017.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [inst : Entrywise α ι]

include inst


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.center_add_radius (I : Interval α) : I.center + I.radius = I.sup := by
  refine Entrywise.ext fun i => ?_
  simp only [Interval.center, Interval.radius, entry_sub, entry_smul, entry_add]
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
