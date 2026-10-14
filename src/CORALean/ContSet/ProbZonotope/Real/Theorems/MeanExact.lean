module

public import CORALean.ContSet.ProbZonotope.Real.Operations.Basic

@[expose] public section

/-!
# `ProbZonotope.mean` is the set of expectations

The expectations of the laws of `P` are exactly the points of `mean P = Z`: the expectation
of `N(μ, Σ)` is `μ`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open MeasureTheory ProbabilityTheory WithLp

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ProbZonotope.mean_exact (P : ProbZonotope n) :
    (fun m => ∫ x, x ∂m) '' P.laws = toLp 2 '' P.mean.construct := by -- --- PROOF ---
  ext y
  constructor
  · rintro ⟨_, ⟨μ, hμ, rfl⟩, rfl⟩
    exact ⟨μ, hμ, (integral_id_multivariateGaussian).symm⟩
  · rintro ⟨μ, hμ, rfl⟩
    exact ⟨_, ⟨μ, hμ, rfl⟩, integral_id_multivariateGaussian⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
