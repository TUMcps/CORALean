import CORALean.ContSet.ProbZonotope.Real.Definitions.GaussPdf
import CORALean.ContSet.ProbZonotope.Real.Theorems.IntegrableExpNegNormSq
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# The standard Gaussian on `ℝⁿ` has density `(2π)^{-n/2} exp(-‖y‖²/2)`

The product of [1, Prop. 1]'s proof, eq. (3), for `Σ = I`, as measures: Mathlib's
`stdGaussian` equals Lebesgue measure with that density. Both are finite and have the
characteristic function `exp(-‖t‖²/2)`, the density's by Mathlib's Gaussian Fourier integral.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems
      using Enclosing Hulls of Probability Density Functions". In Proc. of the European Control
      Conference (ECC), pp. 625-630, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open MeasureTheory ProbabilityTheory Complex
open scoped RealInnerProductSpace _root_.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The density's characteristic function. -/
theorem aux_integral_stdGaussPdf (t : EuclideanSpace ℝ (Fin n)) :
    ∫ y : EuclideanSpace ℝ (Fin n), (stdGaussPdf n y : ℂ) * cexp (↑⟪y, t⟫ * I)
      = cexp (-(‖t‖ : ℂ) ^ 2 / 2) := by -- --- PROOF ---
  have h := GaussianFourier.integral_cexp_neg_mul_sq_norm_add (V := EuclideanSpace ℝ (Fin n))
    (b := (1 / 2 : ℂ)) (by norm_num) I t
  have hint : ∀ y : EuclideanSpace ℝ (Fin n), (stdGaussPdf n y : ℂ) * cexp (↑⟪y, t⟫ * I)
      = ((2 * π : ℝ) : ℂ) ^ (-(n : ℂ) / 2) * cexp (-(1/2 : ℂ) * ‖y‖ ^ 2 + I * ⟪t, y⟫) := by
    intro y
    simp only [stdGaussPdf, ofReal_mul, ofReal_exp]
    rw [ofReal_cpow (by positivity), mul_assoc, ← Complex.exp_add, real_inner_comm]
    push_cast
    ring_nf
  simp_rw [hint]
  rw [integral_const_mul, h, finrank_euclideanSpace, Fintype.card_fin]
  -- `(2π)^{-n/2} (2π)^{n/2} = 1`
  have h2 : (↑π / (1 / 2) : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
  have hne : ((2 * π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  rw [h2, ← mul_assoc, ← cpow_add _ _ hne]
  simp only [neg_div, neg_add_cancel, cpow_zero, one_mul, I_sq]
  congr 1
  ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem stdGaussian_eq_withDensity :
    stdGaussian (EuclideanSpace ℝ (Fin n))
      = volume.withDensity (fun y => ENNReal.ofReal (stdGaussPdf n y)) := by -- --- PROOF ---
  have hpos : ∀ y, 0 ≤ stdGaussPdf n y := fun y => by unfold stdGaussPdf; positivity
  have hmeas : Measurable (fun y => ENNReal.ofReal (stdGaussPdf n y)) := by
    unfold stdGaussPdf; fun_prop
  have hint : Integrable (stdGaussPdf n) := integrable_exp_neg_norm_sq_half.const_mul _
  haveI : IsFiniteMeasure (volume.withDensity (fun y => ENNReal.ofReal (stdGaussPdf n y))) :=
    isFiniteMeasure_withDensity_ofReal hint.hasFiniteIntegral
  -- equal characteristic functions
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_stdGaussian, charFun_apply,
    integral_withDensity_eq_integral_toReal_smul hmeas (by simp), ← aux_integral_stdGaussPdf t]
  congr 1
  funext y
  rw [ENNReal.toReal_ofReal (hpos y), Complex.real_smul]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
