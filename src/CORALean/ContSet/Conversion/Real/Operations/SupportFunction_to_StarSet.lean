module

public import CORALean.ContSet.StarSet.Real.Operations.OfPred
public import CORALean.ContSet.SupportFunction.Real.SupportFunction

@[expose] public section

/-!
# A support function as a star set

The star set whose predicate is the support function itself, center `0`, the identity basis and a
box `D` (`StarSet.ofPred`): the arrow of [1, Fig. 1 (Support Functions → Star Sets)], a star set's
predicate being any representation in coefficient space. A star set carries a finite box, so it is
the support function's set exactly where that set is bounded, `D` any box around it.

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


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `S` as a star set on the box `D`: its own set as the predicate on the coefficients, which are
the point. -/
def SupportFunction.starSet (S : SupportFunction (Vec ℝ n)) (D : Interval (Vec ℝ n)) :
    StarSet (fun m => SupportFunction (Vec ℝ m)) n :=
  StarSet.ofPred (P := fun m => SupportFunction (Vec ℝ m)) D S

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
