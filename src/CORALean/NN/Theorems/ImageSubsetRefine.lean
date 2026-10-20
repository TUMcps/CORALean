module

public import CORALean.NN.Operations.Refine
public import CORALean.NN.Theorems.ImageSubsetEncloseAt

@[expose] public section

/-!
# Refining one neuron keeps the enclosure

Split out of `EncloseAtOuter.lean` (issue #62): one of five genuinely public
declarations there, none used outside the file, so split one file each.

Refining any neuron keeps the enclosure [1, Def. 4.4], which is what leaves
the ranking a ranking: a wrong choice costs precision and never correctness.

## Inputs
* `rn` – refinable network
* `sch` – schedule of order patterns
* `l` – layer index
* `j` – neuron index
* `X` – input set

## Hypotheses
* none

## Conclusion
* the exact image lies in the enclosure after refining the neuron

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

theorem RefinableNetwork.image_subset_refine (rn : RefinableNetwork S n m)
    (sch : Schedule) (l j : ℕ) (X : S n) :
    rn.image (construct X) ⊆ construct (rn.encloseAt (Schedule.refine sch l j) X) :=
  rn.image_subset_encloseAt _ X

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
