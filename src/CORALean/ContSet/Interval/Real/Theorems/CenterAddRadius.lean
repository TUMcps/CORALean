import CORALean.ContSet.Interval.Real.Operations.Center
import CORALean.ContSet.Interval.Real.Operations.Radius
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# `Interval.center_add_radius`

The centre plus the half-width is the upper bound: the split `center ± radius` gives the box back.
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

theorem Interval.center_add_radius (I : Interval α) : I.center + I.radius = I.sup := by
  refine Entrywise.ext fun i => ?_
  simp only [Interval.center, Interval.radius, entry_sub, entry_smul, entry_add]
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
