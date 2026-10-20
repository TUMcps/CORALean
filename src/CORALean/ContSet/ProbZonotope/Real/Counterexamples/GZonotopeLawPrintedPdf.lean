module

public import CORALean.ContSet.ProbZonotope.Real.Definitions.GZonotopeLaw
public import CORALean.ContSet.ProbZonotope.Real.Definitions.GaussPdf
public import CORALean.ContSet.ProbZonotope.Real.Theorems.IntegrableExpNegNormSq
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# [1, Prop. 1]'s printed density is not a density

In `ℝ¹` with the two generators `G = [1 0]` (`q = 2 > n = 1`, `Σ = 1`), [1, Prop. 1] prints
`f(x) = (2π)^{-1} exp(-x²/2)`, whose integral is `(2π)^{-1/2} < 1`. The law of `c + G N` is a
probability measure, so it is not Lebesgue measure with that density. The exponent of `2π` has
to be the dimension `n`, not the number of generators `q` (`GZonotopeLawDensity`).

## Inputs
* none

## Hypotheses
* none

## Conclusion
* [1, Prop. 1]'s printed density is not a density

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

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped _root_.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem gZonotopeLaw_printedGaussPdf_counterexample : -- --- CONCL ---
    let G : Mat ℝ 1 2 := !![1, 0]
    gZonotopeLaw 0 G ≠ volume.withDensity
      (fun x => ENNReal.ofReal (printedGaussPdf 2 0 (G * Gᵀ) x)) := by -- --- PROOF ---
  intro G heq
  have hS : G * Gᵀ = 1 := by
    ext i j; fin_cases i; fin_cases j; simp [G, Matrix.mul_apply, Fin.sum_univ_two]
  have hpdf : ∀ x : EuclideanSpace ℝ (Fin 1), printedGaussPdf 2 0 (G * Gᵀ) x
      = (2 * π)⁻¹ * Real.exp (-‖x‖ ^ 2 / 2) := by
    intro x
    rw [hS]
    simp only [printedGaussPdf, det_one, Real.one_rpow, mul_one, inv_one, one_mulVec, sub_zero]
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [dotProduct, sq]
    rw [Real.rpow_neg_one, mul_inv, mul_comm]
  have hmeas : Measurable
      (fun β : EuclideanSpace ℝ (Fin 2) => toLp 2 ((0 : Vec ℝ 1) + G *ᵥ ofLp β)) := by
    fun_prop
  -- the law has mass `1`, the printed density `(2π)^{-1/2}`
  have h1 : gZonotopeLaw 0 G Set.univ = 1 := by
    haveI : IsProbabilityMeasure (gZonotopeLaw 0 G) :=
      Measure.isProbabilityMeasure_map hmeas.aemeasurable
    exact measure_univ
  rw [heq, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
  simp_rw [hpdf] at h1
  -- the mass is `(2π)⁻¹ (2π)^{1/2}`, below `1`
  have hint : Integrable
      (fun x : EuclideanSpace ℝ (Fin 1) => (2 * π)⁻¹ * Real.exp (-‖x‖ ^ 2 / 2)) :=
    integrable_exp_neg_norm_sq_half.const_mul _
  have hb : (fun x : EuclideanSpace ℝ (Fin 1) => Real.exp (-‖x‖ ^ 2 / 2))
      = fun x => Real.exp (-(1 / 2) * ‖x‖ ^ 2) := by funext x; ring_nf
  rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => by positivity),
    integral_const_mul, hb, GaussianFourier.integral_rexp_neg_mul_sq_norm (by norm_num),
    finrank_euclideanSpace, Fintype.card_fin, ENNReal.ofReal_eq_one] at h1
  have h2 : (π / (1 / 2) : ℝ) = 2 * π := by ring
  rw [h2] at h1
  have hgt : (1 : ℝ) < 2 * π := by linarith [Real.two_le_pi]
  have hlt : (2 * π) ^ ((1 : ℕ) / 2 : ℝ) < (2 * π) ^ (1 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt hgt (by norm_num)
  rw [Real.rpow_one] at hlt
  have hpos : (0 : ℝ) < 2 * π := by positivity
  have : (2 * π)⁻¹ * (2 * π) ^ ((1 : ℕ) / 2 : ℝ) < 1 := by
    rw [inv_mul_lt_iff₀ hpos, mul_one]; exact hlt
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
