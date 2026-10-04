import CORALean.ContSet.ZonoBundle.Real.Theorems.ExistsConZonotope
import CORALean.ContSet.ConZonotope.Real.Theorems.ExistsConstructEqIffHPolytope

/-!
# A bundle is a polytope

`representsa_(zB, 'polytope')` is `true`: constrained zonotopes are the bounded halfspace
descriptions (Scott et al.), and a bundle with a member is one.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.exists_hPolytope (zB : ZonoBundle (Vec ℝ n)) (hk : 0 < zB.k) :
    ∃ P : HPolytope (Vec ℝ n), P.construct = zB.construct := by
  obtain ⟨P, hP, -⟩ := ConZonotope.exists_construct_eq_iff_hPolytope.mp
    (zB.exists_conZonotope hk)
  exact ⟨P, hP⟩


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
