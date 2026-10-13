module

public import CORALean.ContSet.ProbZonotope.Real.Operations.ReduceGirard
public import CORALean.ContSet.Zonotope.Real.Theorems.ReduceGirardOuter

@[expose] public section

/-!
# `ProbZonotope.reduceGirard` over-approximates the family of laws

Every law `N(μ, Σ)`, `μ ∈ Z`, of `P` is a law of the reduced one, as the reduced zonotope
contains `Z` (`reduceGirard_outer`) and the covariance is unchanged. Not equal: the reduced
zonotope has more means.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ProbZonotope.reduceGirard_laws_outer (P : ProbZonotope n) (o : ℕ) :
    P.laws ⊆ (P.reduceGirard o).laws := by
  rintro _ ⟨μ, hμ, rfl⟩
  exact ⟨μ, Zonotope.reduceGirard_outer P.Z o hμ, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
