module

public import CORALean.ContSet.Conversion.Real.Operations.SupportFunction_to_StarSet
public import CORALean.ContSet.StarSet.Real.Theorems.OfPredExact
public import CORALean.ContSet.SupportFunction.Real.Instances

@[expose] public section

/-!
# Every support function is a star set

[1, Fig. 1 (Support Functions → Star Sets)]: the star set `SupportFunction.starSet` denotes what the
support function denotes, exactly, through `StarSet.ofPred_exact`. So every closed convex set,
which a support function denotes (`SupportFunction.ofSet_exact`), is a star set.

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Fig. 1 (Support Functions → Star Sets)]: the star set of a support function denotes its
set. -/
theorem SupportFunction.starSet_exact (S : SupportFunction (Vec ℝ n)) :
    S.starSet.construct = S.construct :=
  StarSet.ofPred_exact (P := fun m => SupportFunction (Vec ℝ m)) S

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
