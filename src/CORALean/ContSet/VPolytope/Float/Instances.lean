import CORALean.ContSet.VPolytope.Float.Theorems.API

/-!
# What the float `VPolytope` instantiates

The same three the exact layer does, `reduce` again the identity. `ContSet` comes
from `InflatedContSet` and is not declared here.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ========================================  INSTANCES  ========================================= --

instance : Plus (VPolytope 𝕋 n) (Vec ℝ n) where
  plus P₁ P₂ := (VPolytope.plus P₁ P₂).materialise
  plus_outer P₁ P₂ := by
    rw [VPolytope.materialise_eq]
    exact VPolytope.plus_outer P₁ P₂

instance : LinComb (VPolytope 𝕋 n) (Vec ℝ n) where
  linComb P₁ P₂ := (VPolytope.linComb P₁ P₂).materialise
  linComb_outer P₁ P₂ := by
    rw [VPolytope.materialise_eq]
    exact VPolytope.linComb_outer P₁ P₂

-- `reduce` is the identity: a vertex list has no ranking to run
instance : Reduce (VPolytope 𝕋 n) (Vec ℝ n) where
  reduce P _ := P.materialise
  reduce_outer P _ := by
    rw [VPolytope.materialise_eq]

instance : Mtimes (Mat 𝕋) (VPolytope 𝕋) where
  mtimes M P := (VPolytope.mtimes M P).materialise
  mtimes_outer M P := by
    simp only [ContSet.construct_mat, Set.biUnion_singleton, VPolytope.materialise_eq]
    exact VPolytope.mtimes_outer M P

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
