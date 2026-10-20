module

public import CORALean.ContSet.ProbZonotope.Real.Operations.Mtimes

@[expose] public section

/-!
# The image of a Gaussian under a linear map

`M N(a, Σ) = N(M a, M Σ Mᵀ)` for a positive semidefinite covariance, by characteristic functions
(`⟨Mx, t⟩ = ⟨x, Mᵀt⟩`).

## Inputs
* `M` – `m × n` matrix
* `a` – point
* `S` – `n × n` matrix

## Hypotheses
* `hS` – `S.PosSemidef`

## Conclusion
* a linear map `L` of a Gaussian is the Gaussian with mean `La` and covariance `LΣLᵀ`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open MeasureTheory ProbabilityTheory Matrix WithLp Complex
open scoped RealInnerProductSpace

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `L N(a, Σ) = N(La, LΣLᵀ)`. -/
theorem map_multivariateGaussian (M : Mat ℝ m n) (a : EuclideanSpace ℝ (Fin n))
    {S : Mat ℝ n n} (hS : S.PosSemidef) : -- --- CONCL ---
    (multivariateGaussian a S).map (fun x => toLp 2 (M *ᵥ ofLp x))
      = multivariateGaussian (toLp 2 (M *ᵥ ofLp a)) (M * S * Mᵀ) := by -- --- PROOF ---
  have hmeas : Measurable (fun x : EuclideanSpace ℝ (Fin n) => toLp 2 (M *ᵥ ofLp x)) := by
    fun_prop
  have hMS : (M * S * Mᵀ).PosSemidef := by
    simpa [Matrix.mul_assoc] using hS.mul_mul_conjTranspose_same M
  haveI : IsProbabilityMeasure ((multivariateGaussian a S).map
      (fun x => toLp 2 (M *ᵥ ofLp x))) := Measure.isProbabilityMeasure_map hmeas.aemeasurable
  -- `⟨Mx, t⟩ = ⟨x, Mᵀt⟩`
  have hin : ∀ (x : EuclideanSpace ℝ (Fin n)) (t : EuclideanSpace ℝ (Fin m)),
      ⟪toLp 2 (M *ᵥ ofLp x), t⟫ = ⟪x, toLp 2 (Mᵀ *ᵥ ofLp t)⟫ := by
    intro x t
    simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    rw [dotProduct_mulVec, mulVec_transpose, dotProduct_comm]
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_apply, integral_map hmeas.aemeasurable (by fun_prop)]
  simp_rw [hin]
  rw [← charFun_apply, charFun_multivariateGaussian hS, charFun_multivariateGaussian hMS]
  congr 1
  have h1 : ⟪toLp 2 (Mᵀ *ᵥ ofLp t), a⟫ = ⟪t, toLp 2 (M *ᵥ ofLp a)⟫ := by
    rw [real_inner_comm, ← hin, real_inner_comm]
  have h2 : ofLp t ⬝ᵥ (M * S * Mᵀ) *ᵥ ofLp t = (Mᵀ *ᵥ ofLp t) ⬝ᵥ S *ᵥ (Mᵀ *ᵥ ofLp t) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]
  rw [h1, h2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
