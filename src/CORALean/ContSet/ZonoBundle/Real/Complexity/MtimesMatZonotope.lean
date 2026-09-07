import CORALean.ContSet.ZonoBundle.Real.Operations.MtimesMatZonotope
import CORALean.ContSet.Zonotope.Real.Complexity.MtimesMatZonotope

/-!
# `ZonoBundle.mtimesMatZonotope`'s counts

The bundle size is unchanged, as `mtimes`'s is. The second-order count is not:
`Zonotope.mtimesMatZonotope_h` is quadratic, so each component pays
`M.h * (zB.Z i).h` new generators on top of the two operands' own — the price
of keeping the matrix's correlations instead of boxing them away. `rfl` against
both structure instances.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.mtimesMatZonotope_k (M : Zonotope (Mat ℝ m n)) (zB : ZonoBundle (Vec ℝ n)) :
    (ZonoBundle.mtimesMatZonotope M zB).k = zB.k := rfl

theorem ZonoBundle.mtimesMatZonotope_Z_h (M : Zonotope (Mat ℝ m n)) (zB : ZonoBundle (Vec ℝ n))
    (i : Fin zB.k) : ((ZonoBundle.mtimesMatZonotope M zB).Z i).h
      = M.h + (zB.Z i).h + M.h * (zB.Z i).h := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
