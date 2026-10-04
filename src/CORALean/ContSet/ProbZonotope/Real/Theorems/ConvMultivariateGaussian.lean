import CORALean.ContSet.ProbZonotope.Real.Operations.Plus

/-!
# The convolution of two Gaussians

`N(a, Σ₁) ∗ N(b, Σ₂) = N(a + b, Σ₁ + Σ₂)` for positive semidefinite covariances, by characteristic
functions.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open MeasureTheory ProbabilityTheory Matrix WithLp Complex
open scoped RealInnerProductSpace

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `N(a, Σ₁) ∗ N(b, Σ₂) = N(a + b, Σ₁ + Σ₂)`. -/
theorem conv_multivariateGaussian (a b : EuclideanSpace ℝ (Fin n)) {S₁ S₂ : Mat ℝ n n}
    (h₁ : S₁.PosSemidef) (h₂ : S₂.PosSemidef) :
    multivariateGaussian a S₁ ∗ multivariateGaussian b S₂
      = multivariateGaussian (a + b) (S₁ + S₂) := by -- --- PROOF ---
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_conv, charFun_multivariateGaussian h₁, charFun_multivariateGaussian h₂,
    charFun_multivariateGaussian (h₁.add h₂), ← Complex.exp_add, inner_add_right, add_mulVec,
    dotProduct_add]
  congr 1
  push_cast
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
