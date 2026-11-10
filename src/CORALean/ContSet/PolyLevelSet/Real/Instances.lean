module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.AndExact

@[expose] public section

/-!
# What `PolyLevelSet` instantiates

`ContSetLike`, which is also what makes it a star set's predicate (`StarSet PolyLevelSet n`), and
`Intersection` by stacking the rows, exact although the class asks only for an outer bound. The
rest is `LevelSet`'s, through `PolyLevelSet.levelSet`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ========================================  INSTANCES  ========================================= --

instance : ContSetLike (PolyLevelSet n) (Vec ℝ n) := ⟨PolyLevelSet.toSet⟩

instance : Intersection (PolyLevelSet n) (Vec ℝ n) where
  intersection := PolyLevelSet.and_
  intersection_outer P₁ P₂ := (PolyLevelSet.and_exact P₁ P₂).symm.subset

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
