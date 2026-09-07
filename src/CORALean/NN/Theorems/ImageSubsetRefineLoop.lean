import CORALean.NN.Operations.RefineLoop
import CORALean.NN.Theorems.ImageSubsetPropagateAt

/-!
# The refinement loop keeps the enclosure

Split out of `PropagateAtOuter.lean` (issue #62): one of five genuinely public
declarations there, none used outside the file, so split one file each.

So does the loop, at every `pick` and every number of steps.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem RefinableNetwork.image_subset_refineLoop (rn : RefinableNetwork S n m)
    (pick : Schedule → ℕ × ℕ) (sch : Schedule) (k : ℕ) (X : S n) :
    rn.image (construct X) ⊆ construct (rn.propagateAt (Schedule.refineLoop pick sch k) X) :=
  rn.image_subset_propagateAt _ X

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
