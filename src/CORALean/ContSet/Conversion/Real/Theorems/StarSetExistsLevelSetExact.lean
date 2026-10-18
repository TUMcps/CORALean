module

public import CORALean.ContSet.LevelSet.Real.Theorems.ExistsConstructEq
public import CORALean.ContSet.StarSet.Real.StarSet

@[expose] public section

/-!
# Every star set is a level set

[1, Fig. 1 (Star Sets ↔ Level Sets)], from star sets to level sets, at any predicate: a level set
denotes any set, the zero set of the set's indicator (`LevelSet.exists_construct_eq`), so it
denotes the star set's. The level set is found, not computed: eliminating the coefficients from
`x = c + G α` and the predicate is no operation of either representation. The other direction is
`LevelSet.starSet_exact`, so the two classes denote the same sets.

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

open ContSet


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Fig. 1 (Star Sets ↔ Level Sets)]: a star set, at any predicate, is a level set. -/
theorem StarSet.exists_levelSet_exact {P : ℕ → Type} [∀ m, ContSet (P m) (Vec ℝ m)] {n : ℕ}
    (s : StarSet P n) : ∃ L : LevelSet n, L.construct = s.construct :=
  LevelSet.exists_construct_eq s.construct

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
