module

public import CORALean.ContSet.ProbZonotope.Float.Operations.Mean
public import CORALean.ContSet.ProbZonotope.Real.Theorems.MeanExact

@[expose] public section

/-!
# `ProbZonotope.mean` bounds the means

Outer: the expectation of every law of `P` lies in the mean zonotope. Not exact: the covariance
interval may hold no positive semidefinite matrix, leaving no law at all.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open MeasureTheory ProbabilityTheory Matrix WithLp FloatOps SoundFloatArithmetic
open scoped Pointwise

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ProbZonotope.mean_outer (P : ProbZonotope 𝕋 n) :
    (fun m => ∫ x, x ∂m) '' P.laws ⊆ toLp 2 '' P.mean.construct := by
  rintro _ ⟨_, ⟨μ, hμ, S, hS, hp, rfl⟩, rfl⟩
  exact ⟨μ, hμ, integral_id_multivariateGaussian.symm⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
