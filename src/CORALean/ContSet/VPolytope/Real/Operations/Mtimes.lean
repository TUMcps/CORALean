import CORALean.ContSet.VPolytope.Real.VPolytope

/-!
# `VPolytope.mtimes`

CORA's `@polytope/mtimes` on a vertex description: `map` at `A *ᵥ ·`, spelt with
`*ᵥ` because that is the form every caller states its matrix in.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


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
