module

public import CORALean.ContSet.Conversion.Real.Operations.LevelSet_to_StarSet
public import CORALean.ContSet.StarSet.Real.Theorems.OfPredExact
public import CORALean.ContSet.LevelSet.Real.Instances

@[expose] public section

/-!
# Every level set is a star set

[1, Fig. 1 (Star Sets ↔ Level Sets)], from level sets to star sets: the star set
`LevelSet.starSet` denotes what the level set denotes, exactly, through `StarSet.ofPred_exact`.
The other direction is `StarSet.exists_levelSet_exact`.

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

/-- [1, Fig. 1 (Star Sets ↔ Level Sets)]: the star set of a level set denotes its set. -/
theorem LevelSet.starSet_exact (L : LevelSet n) : L.starSet.construct = L.construct :=
  StarSet.ofPred_exact L

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
