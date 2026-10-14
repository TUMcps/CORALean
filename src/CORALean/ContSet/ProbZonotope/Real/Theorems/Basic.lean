module

public import CORALean.ContSet.ProbZonotope.Real.Operations.VPolytope

@[expose] public section

/-!
# `ContSet/ProbZonotope/Real/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real

variable {n : ℕ}


-- ==============================  `ProbZonotope.vPolytope_exact`  ============================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The polytope is the mean zonotope `Z`, exactly: not the confidence set of the probabilistic
generators, which CORA's `polytope` and `vertices_` ignore. -/
theorem ProbZonotope.vPolytope_exact (P : ProbZonotope n) :
    P.vPolytope.construct = P.Z.construct :=
  P.Z.vPolytope_exact

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
