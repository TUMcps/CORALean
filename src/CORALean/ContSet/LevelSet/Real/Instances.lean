import CORALean.ContSet.ContSet.ContSet
import CORALean.ContSet.LevelSet.Real.Theorems.API

/-!
# What `LevelSet` instantiates

`ContSet`, and `Intersection` by stacking the constraints, exact even though the class asks only
for an outer bound. Nothing else: a level set is not convex, compact or closed under a sum, and
`Mtimes` is a statement about every matrix an operand denotes, which for a singular one is no
preimage; the invertible case is `LevelSet.mtimes_exact`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ========================================  INSTANCES  ========================================= --

instance : ContSet (LevelSet n) (Vec ℝ n) := ⟨LevelSet.construct⟩

instance : Intersection (LevelSet n) (Vec ℝ n) where
  intersection := LevelSet.and_
  intersection_outer L₁ L₂ := (LevelSet.and_exact L₁ L₂).symm.subset

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
