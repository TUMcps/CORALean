module

public import CORALean.ContSet.Conversion.Real.Operations.LevelSet_to_StarSet
public import CORALean.ContSet.StarSet.Real.Theorems.OfPredExact
public import CORALean.ContSet.LevelSet.Real.Instances

@[expose] public section

/-!
# Every bounded level set is a star set

[1, Fig. 1 (Star Sets ↔ Level Sets)], from level sets to star sets: the star set
`LevelSet.starSet` on a box around the level set denotes what the level set denotes, exactly,
through `StarSet.ofPred_exact`. A star set's box is finite, so an unbounded level set is none.
The other direction is `StarSet.exists_levelSet_exact`.

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

/-- [1, Fig. 1 (Star Sets ↔ Level Sets)]: the star set of a level set on a box around it denotes
its set. -/
theorem LevelSet.starSet_exact (L : LevelSet n) {D : Interval (Vec ℝ n)}
    (hD : L.construct ⊆ D.construct) : (L.starSet D).construct = L.construct :=
  (StarSet.ofPred_exact D L).trans (Set.inter_eq_right.mpr hD)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
