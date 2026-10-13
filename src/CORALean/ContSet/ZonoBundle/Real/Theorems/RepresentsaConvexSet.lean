module

public import CORALean.ContSet.ZonoBundle.Real.Theorems.Convex

@[expose] public section

/-!
# A bundle is convex

`representsa_(zB, 'convexSet')` is `true`: an intersection of convex zonotopes is convex.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.representsa_convexSet (zB : ZonoBundle (Vec ℝ n)) :
    Convex ℝ zB.construct :=
  zB.convex_construct


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
