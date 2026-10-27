module

public import CORALean.ContSet.VPolytope.Real.VPolytope

@[expose] public section

/-!
# `VPolytope.plus`

CORA's `@polytope/plus` on a vertex description: every vertex of one added to
every vertex of the other, so the count multiplies. Exact, and the operation
vertices are for — a halfspace description has no counterpart.

`finProdFinEquiv` is what keeps the index a single `Fin`, matching the field.

The vertex form of the Minkowski sum, [1, Eq. 25].

## Inputs
* `P₁` – first polytope
* `P₂` – second polytope

## Output
* polytope of all sums of a vertex of each

## References

* [1] [M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". Proceedings of the 11th Int. Workshop on Applied Verification for
      Continuous and Hybrid Systems,
      2024.](../../../../../../references/2024/wetzlinger-arch-polyhedral-operations.md)
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
