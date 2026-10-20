module

public import CORALean.ContSet.Interval.Real.Interval
public import CORALean.ContSet.StarSet.Real.Operations.OfPred
public import CORALean.ContSet.LevelSet.Real.LevelSet

@[expose] public section

/-!
# A level set as a star set

The star set whose predicate is the level set itself, center `0`, the identity basis and a box `D`
(`StarSet.ofPred`): one direction of [1, Fig. 1 (Star Sets ↔ Level Sets)], a star set's predicate
being any representation in coefficient space. A star set carries a finite box, so it is the level
set exactly where the level set is bounded, `D` any box around it.

## Inputs
* `L` – level set
* `D` – box of coefficients

## Output
* star set on `D` with the constraints as predicate

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

/-- `L` as a star set on the box `D`: its own constraints as the predicate on the coefficients. -/
def LevelSet.starSet (L : LevelSet n) (D : Interval (Vec ℝ n)) : StarSet LevelSet n :=
  StarSet.ofPred D L

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
