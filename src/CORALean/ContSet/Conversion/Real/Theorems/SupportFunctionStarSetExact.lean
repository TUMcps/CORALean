module

public import CORALean.ContSet.Conversion.Real.Operations.SupportFunction_to_StarSet
public import CORALean.ContSet.StarSet.Real.Theorems.OfPredExact
public import CORALean.ContSet.SupportFunction.Real.Instances

@[expose] public section

/-!
# Every bounded support function is a star set

[1, Fig. 1 (Support Functions → Star Sets)]: the star set `SupportFunction.starSet` on a box around
the support function's set denotes that set, exactly, through `StarSet.ofPred_exact`. So every
compact convex set, which a support function denotes (`SupportFunction.ofSet_exact`), is a star
set; a star set's box is finite, so an unbounded one is none.

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Fig. 1 (Support Functions → Star Sets)]: the star set of a support function on a box around
its set denotes that set. -/
theorem SupportFunction.starSet_exact (S : SupportFunction (Vec ℝ n)) {D : Interval (Vec ℝ n)}
    (hD : S.construct ⊆ D.construct) : (S.starSet D).construct = S.construct :=
  (StarSet.ofPred_exact (P := fun m => SupportFunction (Vec ℝ m)) D S).trans
    (Set.inter_eq_right.mpr hD)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
