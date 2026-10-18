module

public import CORALean.ContSet.StarSet.Real.Operations.OfPred
public import CORALean.ContSet.LevelSet.Real.LevelSet

@[expose] public section

/-!
# A level set as a star set

The star set whose predicate is the level set itself, center `0` and the identity basis
(`StarSet.ofPred`): one direction of [1, Fig. 1 (Star Sets ↔ Level Sets)], a star set's predicate
being any representation in coefficient space.

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


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `L` as a star set: its own constraints as the predicate on the coefficients. -/
def LevelSet.starSet (L : LevelSet n) : StarSet LevelSet n :=
  StarSet.ofPred L

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
