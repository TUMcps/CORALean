module

public import CORALean.ContSet.Interval.Real.Theorems.Basic
public import CORALean.ContSet.Interval.Real.Theorems.LeIffSubset
public import Mathlib.Order.BourbakiWitt

@[expose] public section

/-!
# `Interval.isequal` decides equality of the denoted sets

For two nonempty boxes equal sets give equal bounds, so `isequal` holds exactly when the sets agree.
Two crossed boxes are both `∅` and need not have equal bounds, so nonemptiness is needed.

## Inputs
* `I` – first interval
* `J` – second interval

## Hypotheses
* `hI` – `I` nonempty
* `hJ` – `J` nonempty

## Conclusion
* the equality test holds iff the two sets coincide
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


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
