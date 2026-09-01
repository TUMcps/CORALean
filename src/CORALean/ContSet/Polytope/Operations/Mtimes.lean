import CORALean.ContSet.Polytope.Operations.Map

/-!
# `VPolytope.mtimes`

CORA's `@polytope/mtimes` on a vertex description: `map` at `A *ᵥ ·`, spelt with
`*ᵥ` because that is the form every caller states its matrix in.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {n m : ℕ}

def VPolytope.mtimes (M : Mat ℝ m n) (P : VPolytope (Vec ℝ n)) : VPolytope (Vec ℝ m) where
  k := P.k
  V := fun j => M *ᵥ P.V j

/-- True by `rfl`, and what lets `mtimes` inherit `map`'s exactness. -/
theorem VPolytope.mtimes_eq_map (M : Mat ℝ m n) (P : VPolytope (Vec ℝ n)) :
    VPolytope.mtimes M P = P.map (Matrix.mulVecLin M) := rfl

end CORALean.Real
