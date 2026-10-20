module

public import CORALean.Global.GaussMomentRoot
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

@[expose] public section

/-!
# Absolute moments of a Gaussian projection

[1, Thm. 15 (accuracy)]: for `g` a standard Gaussian vector and `a` a fixed vector,
`E|⟨a, g⟩|^k = ‖a‖^k γ_k^k`, `γ_k` the constant of Eq. 31 (`gaussMomentRoot`). `⟨a, g⟩` is
a centered Gaussian of variance `‖a‖²` (Mathlib's `stdGaussian` is Gaussian, and the variance
of a functional is its squared norm), so it is `‖a‖` times a standard normal; and
`E|g|^k = 2 ∫₀^∞ x^k e^{-x²/2} / √(2π) dx = 2^{k/2} Γ((k+1)/2) / √π` by the Gamma integral.

## Inputs
* `E` – inner product space
* `a` – fixed vector
* `k` – moment order

## Hypotheses
* `hk` – the moment order is positive

## Conclusion
* the projection's absolute moment is the vector's norm to the order times the Gaussian constant

## References

* [1] A. Kulmburg, L. Schäfer and M. Althoff. "Approximability of the Containment Problem for
      Zonotopes and Ellipsotopes". IEEE Transactions on Automatic Control, 2025.
      doi:10.1109/TAC.2025.3583624. arXiv:2404.11185.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `E|g|^k = γ_k^k` for a standard normal `g`. -/
theorem aux_integral_abs_rpow_gaussianReal {k : ℝ} (hk : 0 < k) :
    ∫ x, |x| ^ k ∂(gaussianReal 0 1) = gaussMomentRoot k ^ k := by -- --- PROOF ---
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  -- the integrand is even
  have heven : (fun x : ℝ => gaussianPDFReal 0 1 x • |x| ^ k) =
      fun x => (fun y : ℝ =>
        (Real.sqrt (2 * Real.pi))⁻¹ * (y ^ k * Real.exp (-(1 / 2) * y ^ (2 : ℝ)))) |x| := by
    funext x
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, smul_eq_mul]
    rw [Real.rpow_two, sq_abs]
    ring_nf
  rw [heven, integral_comp_abs
    (f := fun y : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * (y ^ k * Real.exp (-(1 / 2) * y ^ (2 : ℝ)))),
    integral_const_mul,
    integral_rpow_mul_exp_neg_mul_rpow two_pos (by linarith) (by norm_num)]
  unfold gaussMomentRoot
  have hΓ : 0 ≤ Real.Gamma ((k + 1) / 2) := (Real.Gamma_pos_of_pos (by linarith)).le
  rw [one_div k, Real.rpow_inv_rpow (by positivity) hk.ne']
  -- `2 · (2π)^{-1/2} · 2^{(k+1)/2} · ½ = 2^{k/2} / √π`
  have h2 : (1 / 2 : ℝ) ^ (-(k + 1) / 2) = 2 ^ (k / 2) * Real.sqrt 2 := by
    rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num), Real.sqrt_eq_rpow,
      ← Real.rpow_add (by norm_num)]
    ring_nf
  rw [h2, Real.sqrt_mul (by norm_num)]
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hsπ : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  field_simp


-- =======================================  MAIN THEOREM  ======================================= --

theorem integral_abs_inner_rpow_stdGaussian {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (a : E) {k : ℝ} (hk : 0 < k) :
    ∫ g, |⟪a, g⟫| ^ k ∂(stdGaussian E) = ‖a‖ ^ k * gaussMomentRoot k ^ k := by -- --- PROOF ---
  -- `⟨a, g⟩` is `N(0, ‖a‖²)`, the image of `N(0, 1)` under `x ↦ ‖a‖ x`
  have hmap : (stdGaussian E).map (innerSL ℝ a) = (gaussianReal 0 1).map (‖a‖ * ·) := by
    rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
      variance_dual_stdGaussian, innerSL_apply_norm, gaussianReal_map_const_mul, mul_zero,
      mul_one]
    congr 1
    ext
    simp
  have hm : Measurable fun x : ℝ => |x| ^ k := by fun_prop
  calc ∫ g, |⟪a, g⟫| ^ k ∂(stdGaussian E)
      = ∫ x, |x| ^ k ∂((stdGaussian E).map (innerSL ℝ a)) := by
        rw [integral_map (innerSL ℝ a).continuous.aemeasurable
          hm.aestronglyMeasurable]
        rfl
    _ = ∫ x, |‖a‖ * x| ^ k ∂(gaussianReal 0 1) := by
        rw [hmap, integral_map (by fun_prop) hm.aestronglyMeasurable]
    _ = ‖a‖ ^ k * gaussMomentRoot k ^ k := by
        simp_rw [abs_mul, abs_norm, Real.mul_rpow (norm_nonneg a) (abs_nonneg _)]
        rw [integral_const_mul, aux_integral_abs_rpow_gaussianReal hk]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
