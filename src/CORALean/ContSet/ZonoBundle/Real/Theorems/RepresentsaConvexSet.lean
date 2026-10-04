import CORALean.ContSet.ZonoBundle.Real.Theorems.Convex

/-!
# A bundle is convex

`representsa_(zB, 'convexSet')` is `true`: an intersection of convex zonotopes is convex.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.representsa_convexSet (zB : ZonoBundle (Vec ℝ n)) :
    Convex ℝ zB.construct :=
  zB.convex_construct


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
