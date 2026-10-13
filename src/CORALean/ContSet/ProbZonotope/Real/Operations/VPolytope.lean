import CORALean.ContSet.ProbZonotope.Real.ProbZonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_VPolytope

/-!
# `ProbZonotope.vPolytope`

CORA's `polytope` and `vertices_` of a probabilistic zonotope (`@probZonotope/polytope.m`,
`vertices_.m`): both read the zonotope of `Z` alone, `polytope(zonotope(probZ.Z))` and the
vertices of the matrix `Z`, so the covariance plays no part. The polytope here is the
zonotope's corner polytope (`Zonotope.vPolytope`): its hull is the zonotope of possible means,
exact (`Theorems.VPolytopeExact`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def ProbZonotope.vPolytope (P : ProbZonotope n) : VPolytope (Vec ℝ n) :=
  P.Z.vPolytope

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
