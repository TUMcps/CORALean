import CORALean.ContSet.ProbZonotope.Real.Operations.VPolytope

/-!
# `ProbZonotope.vPolytope` is the zonotope of possible means

The polytope is the mean zonotope `Z`, exactly: not the confidence set of the probabilistic
generators, which CORA's `polytope` and `vertices_` ignore.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ProbZonotope.vPolytope_exact (P : ProbZonotope n) :
    P.vPolytope.construct = P.Z.construct :=
  P.Z.vPolytope_exact

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
