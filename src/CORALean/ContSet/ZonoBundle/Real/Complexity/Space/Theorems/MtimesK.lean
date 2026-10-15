module

public import CORALean.ContSet.ZonoBundle.Real.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Real.Complexity.Space.Theorems.Basic

@[expose] public section

/-!
# `ZonoBundle.mtimes`'s counts

`mtimes`'s bundle size: the same `k`, each component mapped on its own. The
second-order count also carries over: `Zonotope.mtimes_h` says the image keeps
each component's generator count too. `rfl` against both structure instances.
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

/-- The `k` count of `mtimes`'s result. -/
theorem ZonoBundle.mtimes_k (M : Mat ℝ m n) (zB : ZonoBundle (Vec ℝ n)) :
    (ZonoBundle.mtimes M zB).k = zB.k := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
