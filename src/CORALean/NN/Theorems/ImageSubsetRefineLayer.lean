import CORALean.NN.Operations.RefineLayer
import CORALean.NN.Theorems.ImageSubsetEncloseAt

/-!
# Refining a whole layer keeps the enclosure

Split out of `EncloseAtOuter.lean` (issue #62): one of five genuinely public
declarations there, none used outside the file, so split one file each.

Refining a whole layer [1, Def. 4.6], the rule that spends more orders for the
same generator count, keeps the enclosure too.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem RefinableNetwork.image_subset_refineLayer (rn : RefinableNetwork S n m)
    (sch : Schedule) (l : ℕ) (X : S n) :
    rn.image (construct X) ⊆ construct (rn.encloseAt (Schedule.refineLayer sch l) X) :=
  rn.image_subset_encloseAt _ X

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
