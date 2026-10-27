module

public import CORALean.ContSet.VPolytope.Real.VPolytope

@[expose] public section

/-!
# `VPolytope.mtimes`

CORA's `@polytope/mtimes` on a vertex description: `map` at `A *ᵥ ·`, spelt with
`*ᵥ` because that is the form every caller states its matrix in.

The vertex form of the linear map, [1, Eq. 23].

## Inputs
* `M` – matrix
* `P` – polytope

## Output
* polytope of the vertices mapped by `M`

## References

* [1] [M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". Proceedings of the 11th Int. Workshop on Applied Verification for
      Continuous and Hybrid Systems,
      2024.](../../../../../../references/2024/wetzlinger-arch-polyhedral-operations.md)
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def VPolytope.mtimes (M : Mat ℝ m n) (P : VPolytope (Vec ℝ n)) : VPolytope (Vec ℝ m) where
  k := P.k
  V := fun j => M *ᵥ P.V j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
