module

public import CORALean.ContSet.VPolytope.Real.VPolytope

@[expose] public section

/-!
# `VPolytope.mtimes`

CORA's `@polytope/mtimes` on a vertex description: `map` at `A *ᵥ ·`, spelt with
`*ᵥ` because that is the form every caller states its matrix in.

The vertex form of the linear map, [1, Eq. 23].

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification for Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
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
