import CORALean.ContSet.VPolytope.Real.VPolytope

/-!
# `VPolytope.plus`

CORA's `@polytope/plus` on a vertex description: every vertex of one added to
every vertex of the other, so the count multiplies. Exact, and the operation
vertices are for — a halfspace description has no counterpart.

`finProdFinEquiv` is what keeps the index a single `Fin`, matching the field.

The vertex form of the Minkowski sum, [1, Eq. 25].

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification for Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def VPolytope.plus (P₁ P₂ : VPolytope α) : VPolytope α where
  k := P₁.k * P₂.k
  V := fun l => P₁.V (finProdFinEquiv.symm l).1 + P₂.V (finProdFinEquiv.symm l).2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
