import CORALean.ContSet.VPolytope.Real.Operations.MtimesMatPolytope

/-!
# `VPolytope.mtimesMatPolytope_k`

`mtimesMatPolytope` is `bilin` at `Matrix.mulVecBilin`, so its count is
`bilin`'s: the matrix's own vertex count times the operand's. `rfl`, by
unfolding the definition rather than restating `bilin_k`.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.mtimesMatPolytope_k (M : VPolytope (Mat ℝ m n)) (P : VPolytope (Vec ℝ n)) :
    (VPolytope.mtimesMatPolytope M P).k = M.k * P.k := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
