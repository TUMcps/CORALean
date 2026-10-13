import CORALean.ContSet.VPolytope.Real.Operations.Mtimes

/-!
# `VPolytope.mtimes_k`

`mtimes` is `map` at `A *ᵥ ·`: the vertex count carries over exactly, one image
vertex per operand vertex. `rfl`, since `Operations/Mtimes.lean` states `k`
directly.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.mtimes_k (M : Mat ℝ m n) (P : VPolytope (Vec ℝ n)) :
    (VPolytope.mtimes M P).k = P.k := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
