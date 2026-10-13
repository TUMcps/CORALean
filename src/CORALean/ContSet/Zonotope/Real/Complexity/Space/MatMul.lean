module

public import CORALean.ContSet.Zonotope.Real.Operations.MatMul

@[expose] public section

/-!
# `Zonotope.matMul_h`

`matMul` is `bilin` at `matMulBilin`, so its count is `bilin`'s: quadratic in
the two operands' generator counts. `rfl`, by unfolding the definition rather
than restating `bilin_h`.

This is what a power of a matrix zonotope pays: `matPow M k` squares the count
at every step, which is why a Taylor order is a cost as well as a tightness.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {p q r : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.matMul_h (M : Zonotope (Mat ℝ p q)) (N : Zonotope (Mat ℝ q r)) :
    (Zonotope.matMul M N).h = M.h + N.h + M.h * N.h := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
