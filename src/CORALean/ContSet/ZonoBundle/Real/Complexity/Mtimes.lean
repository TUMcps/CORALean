import CORALean.ContSet.ZonoBundle.Real.Operations.Mtimes
import CORALean.ContSet.Zonotope.Real.Complexity.Mtimes

/-!
# `ZonoBundle.mtimes`'s counts

`mtimes`'s bundle size: the same `k`, each component mapped on its own. The
second-order count also carries over: `Zonotope.mtimes_h` says the image keeps
each component's generator count too. `rfl` against both structure instances.
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

theorem ZonoBundle.mtimes_k (M : Mat ℝ m n) (zB : ZonoBundle (Vec ℝ n)) :
    (ZonoBundle.mtimes M zB).k = zB.k := rfl

theorem ZonoBundle.mtimes_Z_h (M : Mat ℝ m n) (zB : ZonoBundle (Vec ℝ n)) (i : Fin zB.k) :
    ((ZonoBundle.mtimes M zB).Z i).h = (zB.Z i).h := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
