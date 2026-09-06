import CORALean.ContSet.Zonotope.Real.Operations.MtimesMatZonotope

/-!
# `Zonotope.mtimesMatZonotope_h`

`mtimesMatZonotope` is `bilin` at `Matrix.mulVecBilin`, so its count is
`bilin`'s: quadratic in the two operands' generator counts. `rfl`, by unfolding
the definition rather than restating `bilin_h`.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.mtimesMatZonotope_h (M : Zonotope (Mat ℝ m n)) (Z : Zonotope (Vec ℝ n)) :
    (Zonotope.mtimesMatZonotope M Z).h = M.h + Z.h + M.h * Z.h := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
