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

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

instance : Plus (VPolytope 𝕋 n) (Vec ℝ n) where
  plus := VPolytope.plus
  plus_outer := VPolytope.plus_outer

instance : LinComb (VPolytope 𝕋 n) (Vec ℝ n) where
  linComb := VPolytope.linComb
  linComb_outer := VPolytope.linComb_outer

instance : Reduce (VPolytope 𝕋 n) (Vec ℝ n) where
  reduce P _ := P
  reduce_outer _ _ := subset_rfl

instance : Mtimes (Mat 𝕋) (VPolytope 𝕋) where
  mtimes := VPolytope.mtimes
  mtimes_outer M P := by
    simp only [ContSet.construct_mat, Set.biUnion_singleton]
    exact VPolytope.mtimes_outer M P

end CORALean.Float
