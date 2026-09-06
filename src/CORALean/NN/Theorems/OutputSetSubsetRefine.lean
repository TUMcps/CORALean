import CORALean.NN.Operations.Refine
import CORALean.NN.Theorems.OutputSetSubsetPropagateAt

/-!
# Refining one neuron keeps the enclosure

Split out of `PropagateAtOuter.lean` (issue #62): one of five genuinely public
declarations there, none used outside the file, so split one file each.

Refining any neuron keeps the enclosure [1, Def. 4.4], which is what leaves
the ranking a ranking: a wrong choice costs precision and never correctness.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
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

theorem RefinableNetwork.outputSet_subset_refine (rn : RefinableNetwork S n m)
    (sch : Schedule) (l j : ℕ) (X : S n) :
    rn.outputSet X ⊆ construct (rn.propagateAt (Schedule.refine sch l j) X) :=
  rn.outputSet_subset_propagateAt _ X

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
