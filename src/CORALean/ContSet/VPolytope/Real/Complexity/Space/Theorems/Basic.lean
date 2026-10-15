module

public import CORALean.ContSet.VPolytope.Real.Operations.Mtimes
public import CORALean.ContSet.VPolytope.Real.Operations.MtimesMatPolytope

@[expose] public section

/-!
# `ContSet/VPolytope/Real/Complexity/Space/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- ===================================  `VPolytope.mtimes_k`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `mtimes` is `map` at `A *ᵥ ·`: the vertex count carries over exactly, one image
vertex per operand vertex. `rfl`, since `Operations/Mtimes.lean` states `k`
directly. -/
theorem VPolytope.mtimes_k (M : Mat ℝ m n) (P : VPolytope (Vec ℝ n)) :
    (VPolytope.mtimes M P).k = P.k := rfl


-- =============================  `VPolytope.mtimesMatPolytope_k`  ============================== --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `mtimesMatPolytope` is `bilin` at `Matrix.mulVecBilin`, so its count is
`bilin`'s: the matrix's own vertex count times the operand's. `rfl`, by
unfolding the definition rather than restating `bilin_k`. -/
theorem VPolytope.mtimesMatPolytope_k (M : VPolytope (Mat ℝ m n)) (P : VPolytope (Vec ℝ n)) :
    (VPolytope.mtimesMatPolytope M P).k = M.k * P.k := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
