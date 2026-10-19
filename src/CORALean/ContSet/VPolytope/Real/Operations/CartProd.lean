module

public import CORALean.ContSet.VPolytope.Real.VPolytope
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
# `VPolytope.cartProd`

[1, Eq. 28]: the Cartesian product of two V-polytopes has every point of the first stacked on
every point of the second, `m₁ m₂` points. CORA converts both factors to halfspaces instead
(`@polytope/cartProd_`); this is the vertex form the paper also gives.

## Inputs
* `P₁` – first polytope
* `P₂` – second polytope

## Output
* polytope of the concatenated vertex pairs

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification for Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


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
