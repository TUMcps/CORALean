import CORALean.ContSet.VPolytope.Real.VPolytope
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# `VPolytope.cartProd`

[1, Eq. 28]: the Cartesian product of two V-polytopes has every point of the first stacked on
every point of the second, `m₁ m₂` points. CORA converts both factors to halfspaces instead
(`@polytope/cartProd_`); this is the vertex form the paper also gives.

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification for Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n₁ n₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def VPolytope.cartProd (P₁ : VPolytope (Vec ℝ n₁)) (P₂ : VPolytope (Vec ℝ n₂)) :
    VPolytope (Vec ℝ (n₁ + n₂)) where
  k := P₁.k * P₂.k
  V := fun l => Fin.append (P₁.V (finProdFinEquiv.symm l).1) (P₂.V (finProdFinEquiv.symm l).2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
