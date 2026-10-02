import CORALean.ContSet.Interval.Real.Theorems.IsequalConstructEq
import CORALean.ContSet.Interval.Real.Theorems.LeIffSubset
import Mathlib.Order.BourbakiWitt

/-!
# `Interval.isequal` decides equality of the denoted sets

For two nonempty boxes equal sets give equal bounds, so `isequal` holds exactly when the sets agree.
Two crossed boxes are both `∅` and need not have equal bounds, so nonemptiness is needed.
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

theorem Interval.isequal_iff {I J : Interval α} (hI : I.IsNonempty) (hJ : J.IsNonempty) :
    I.isequal J ↔ I.construct = J.construct :=
  ⟨Interval.construct_eq_of_isequal, fun h =>
    ⟨(Interval.le_iff_subset hI).2 h.subset, (Interval.le_iff_subset hJ).2 h.symm.subset⟩⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
