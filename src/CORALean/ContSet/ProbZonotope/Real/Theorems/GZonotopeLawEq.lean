module

public import CORALean.ContSet.ProbZonotope.Real.Definitions.GZonotopeLaw

@[expose] public section

/-!
# A G-zonotope with certain mean is the Gaussian `N(c, G Gᵀ)`

[1, Prop. 1]'s first half: the random vector `c + G N` of [1, Def. 3] has the multivariate
Gaussian law with mean `c` and covariance `Σ = G Gᵀ`, for any number `q` of generators —
Mathlib's `multivariateGaussian`, which needs no density. Proved by characteristic functions:
`E[exp(i⟨c + Gβ, t⟩)] = exp(i⟨c, t⟩ - ‖Gᵀt‖²/2)` and `‖Gᵀt‖² = tᵀ G Gᵀ t`.

## Inputs
* `c` – center of length `n`
* `G` – `n × q` matrix

## Hypotheses
* none

## Conclusion
* A G-zonotope with certain mean is the Gaussian `N(c, G Gᵀ)`

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems using
      Enclosing Hulls of Probability Density Functions". 2009 European Control Conference (ECC),
      2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open MeasureTheory ProbabilityTheory Matrix WithLp Complex
open scoped RealInnerProductSpace

variable {n q : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `⟨c + Gβ, t⟩ = cᵀt + ⟨β, Gᵀt⟩`. -/
private theorem aux_inner_affine (c : Vec ℝ n) (G : Mat ℝ n q) (β : EuclideanSpace ℝ (Fin q))
    (t : EuclideanSpace ℝ (Fin n)) :
    ⟪toLp 2 (c + G *ᵥ ofLp β), t⟫ = c ⬝ᵥ ofLp t + ⟪β, toLp 2 (Gᵀ *ᵥ ofLp t)⟫ := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  rw [dotProduct_add, dotProduct_comm (ofLp t) c, dotProduct_mulVec, mulVec_transpose]


-- =======================================  MAIN THEOREM  ======================================= --

theorem gZonotopeLaw_eq (c : Vec ℝ n) (G : Mat ℝ n q) : -- --- CONCL ---
    gZonotopeLaw c G = multivariateGaussian (toLp 2 c) (G * Gᵀ) := by -- --- PROOF ---
  have hmeas : Measurable (fun β : EuclideanSpace ℝ (Fin q) => toLp 2 (c + G *ᵥ ofLp β)) := by
    fun_prop
  have hS : (G * Gᵀ).PosSemidef := by simpa using posSemidef_self_mul_conjTranspose G
  haveI : IsProbabilityMeasure (gZonotopeLaw c G) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  -- equal characteristic functions
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_multivariateGaussian hS, gZonotopeLaw, charFun_apply,
    integral_map hmeas.aemeasurable (by fun_prop)]
  have hx : ∀ x : EuclideanSpace ℝ (Fin q), cexp (↑⟪toLp 2 (c + G *ᵥ ofLp x), t⟫ * I)
      = cexp (↑(c ⬝ᵥ ofLp t) * I) * cexp (↑⟪x, toLp 2 (Gᵀ *ᵥ ofLp t)⟫ * I) := by
    intro x
    rw [aux_inner_affine, ofReal_add, add_mul, Complex.exp_add]
  simp_rw [hx]
  rw [integral_const_mul, ← charFun_apply, charFun_stdGaussian, ← Complex.exp_add]
  congr 1
  -- `‖Gᵀt‖² = tᵀ G Gᵀ t`
  have hn : ‖toLp 2 (Gᵀ *ᵥ ofLp t)‖ ^ 2 = ofLp t ⬝ᵥ (G * Gᵀ) *ᵥ ofLp t := by
    rw [EuclideanSpace.real_norm_sq_eq, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]
    simp [dotProduct, sq]
  have hc : ⟪t, toLp 2 c⟫ = c ⬝ᵥ ofLp t := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  rw [hc, ← hn]
  push_cast
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
