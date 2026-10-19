module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.ContSet.PolyLevelSet.Float.Theorems.AndExact

@[expose] public section

/-!
# What `PolyLevelSet` instantiates over a floating-point scalar

`ContSet`, and `Intersection` by stacking the rows, exact although the class asks only for an
outer bound.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ========================================  INSTANCES  ========================================= --

instance : ContSet (PolyLevelSet 𝕋 n) (Vec ℝ n) := ⟨PolyLevelSet.construct⟩

instance : Intersection (PolyLevelSet 𝕋 n) (Vec ℝ n) where
  intersection := PolyLevelSet.and_
  intersection_outer P₁ P₂ := (PolyLevelSet.and_exact P₁ P₂).symm.subset

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
