import CORALean.ContSet.Interval.Real.Operations.Isequal
import CORALean.ContSet.Interval.Real.Theorems.LeSubset

/-!
# `Interval.isequal` gives equal sets

Equal bounds give equal sets, with no hypothesis: containment each way.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.construct_eq_of_isequal {I J : Interval α} (h : I.isequal J) :
    I.construct = J.construct :=
  Set.Subset.antisymm (Interval.le_subset h.1) (Interval.le_subset h.2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
