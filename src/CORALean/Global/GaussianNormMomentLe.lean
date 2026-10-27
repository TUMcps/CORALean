module

public import CORALean.Global.GaussianAbsMoment
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow

@[expose] public section

/-!
# Moments of the `p`-norm of a Gaussian image

The upper half of the Gaussian rounding of [1, Thm. 15 (accuracy)], [1, Thm. 17] and
[1, Thm. 19]: for a standard Gaussian `g`, vectors `bᵢ`, `p > 0` and `0 < s ≤ p`, the `s`-th
moment of `F(g) = (Σᵢ |⟨bᵢ, g⟩|^p)^{1/p}` is at most `(γ_p (Σᵢ ‖bᵢ‖^p)^{1/p})^s`, `γ_p` the
constant of Eq. 31. `F^p = Σᵢ |⟨bᵢ, g⟩|^p` has expectation `γ_p^p Σᵢ ‖bᵢ‖^p`
(`integral_abs_inner_rpow_stdGaussian`), and Jensen's inequality for the convex `t ↦ t^{p/s}`
moves the expectation of `F^s` inside. `F^s` is integrable, being at most `1 + F^p`.

## Inputs
* `l` – number of vectors
* `b` – the vectors
* `p` – norm exponent
* `s` – moment order

## Hypotheses
* `hs` – the moment order is positive
* `hsp` – the moment order is at most the norm exponent

## Conclusion
* the moment of the norm of the Gaussian image is integrable and bounded by the Gaussian constants

## References

* [1] [A. Kulmburg, L. Schäfer and M. Althoff. "Approximability of the Containment Problem for
      Zonotopes and Ellipsotopes". IEEE Transactions on Automatic Control,
      2025.](../../../references/2025/kulmburg-tac-approximability-containment.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `|⟨a, g⟩|^k` is integrable under the standard Gaussian. -/
private theorem aux_gnm_integrable_abs_inner_rpow (a : E) {k : ℝ} (hk : 0 < k) :
    Integrable (fun g => |⟪a, g⟫| ^ k) (stdGaussian E) := by
  have h := (IsGaussian.memLp_dual (stdGaussian E) (innerSL ℝ a) (ENNReal.ofReal k)
    ENNReal.ofReal_ne_top).integrable_norm_rpow'
  simp only [ENNReal.toReal_ofReal hk.le, Real.norm_eq_abs, innerSL_apply_apply] at h
  exact h

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem aux_gnm_continuous_abs_inner_rpow (a : E) {k : ℝ} (hk : 0 ≤ k) :
    Continuous (fun g : E => |⟪a, g⟫| ^ k) :=
  ((continuous_const.inner continuous_id).abs).rpow_const fun _ => Or.inr hk

/-- `t ≤ 1 + t^p` for `t ≥ 0` and `p ≥ 1`. -/
private theorem aux_gnm_le_one_add_rpow {t p : ℝ} (ht : 0 ≤ t) (hp : 1 ≤ p) : t ≤ 1 + t ^ p := by
  rcases le_or_gt t 1 with h | h
  · linarith [Real.rpow_nonneg ht p]
  · have : t ≤ t ^ p := by simpa using Real.rpow_le_rpow_of_exponent_le h.le hp
    linarith

private theorem aux_gnm_gaussMomentRoot_nonneg {p : ℝ} (hp : 0 < p) : 0 ≤ gaussMomentRoot p := by
  unfold gaussMomentRoot
  exact Real.rpow_nonneg (mul_nonneg (by positivity)
    (Real.Gamma_pos_of_pos (by linarith)).le) _


-- =======================================  MAIN THEOREM  ======================================= --

theorem gaussian_norm_moment_le {l : ℕ} (b : Fin l → E) {p s : ℝ} (hs : 0 < s)
    (hsp : s ≤ p) : -- --- CONCL ---
    Integrable (fun g => ((∑ i, |⟪b i, g⟫| ^ p) ^ (1 / p)) ^ s) (stdGaussian E) ∧
      ∫ g, ((∑ i, |⟪b i, g⟫| ^ p) ^ (1 / p)) ^ s ∂(stdGaussian E) ≤
        (gaussMomentRoot p * (∑ i, ‖b i‖ ^ p) ^ (1 / p)) ^ s := by -- --- PROOF ---
  set μ := stdGaussian E
  have hp0 : 0 < p := hs.trans_le hsp
  have hps : 1 ≤ p / s := (one_le_div hs).mpr hsp
  set P : E → ℝ := fun g => ∑ i, |⟪b i, g⟫| ^ p
  set F : E → ℝ := fun g => (P g ^ (1 / p)) ^ s
  have hP0 : ∀ g, 0 ≤ P g := fun g => Finset.sum_nonneg fun i _ => by positivity
  -- `F^{p/s} = P`
  have hFP : ∀ g, F g ^ (p / s) = P g := fun g => by
    simp only [F]
    rw [← Real.rpow_mul (Real.rpow_nonneg (hP0 g) _), ← Real.rpow_mul (hP0 g)]
    field_simp
    exact Real.rpow_one _
  have hF0 : ∀ g, 0 ≤ F g := fun g => Real.rpow_nonneg (Real.rpow_nonneg (hP0 g) _) _
  have hPi : Integrable P μ :=
    integrable_finsetSum _ fun i _ => aux_gnm_integrable_abs_inner_rpow (b i) hp0
  have hFc : Continuous F :=
    ((continuous_finsetSum _ fun i _ => aux_gnm_continuous_abs_inner_rpow (b i)
      hp0.le).rpow_const fun _ => Or.inr (by positivity)).rpow_const fun _ => Or.inr hs.le
  have hFi : Integrable F μ := by
    refine (integrable_const 1 |>.add hPi).mono' hFc.aestronglyMeasurable
      (ae_of_all _ fun g => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hF0 g)]
    exact (aux_gnm_le_one_add_rpow (hF0 g) hps).trans_eq (by rw [hFP]; rfl)
  refine ⟨hFi, ?_⟩
  -- Jensen: `(E F)^{p/s} ≤ E F^{p/s} = E P`
  have hJ : (∫ g, F g ∂μ) ^ (p / s) ≤ ∫ g, P g ∂μ := by
    have := (convexOn_rpow hps).map_integral_le (μ := μ) (f := F)
      (Real.continuous_rpow_const (by positivity)).continuousOn isClosed_Ici
      (ae_of_all _ hF0) hFi (by simpa [Function.comp_def, hFP] using hPi)
    simpa [Function.comp_def, hFP] using this
  have hEP : ∫ g, P g ∂μ = gaussMomentRoot p ^ p * ∑ i, ‖b i‖ ^ p := by
    rw [integral_finsetSum _ fun i _ => aux_gnm_integrable_abs_inner_rpow (b i) hp0,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [integral_abs_inner_rpow_stdGaussian (b i) hp0, mul_comm]
  -- take the `p/s`-th root back
  have hγ := aux_gnm_gaussMomentRoot_nonneg hp0
  have hS : 0 ≤ ∑ i, ‖b i‖ ^ p := Finset.sum_nonneg fun i _ => by positivity
  have hEF0 : 0 ≤ ∫ g, F g ∂μ := integral_nonneg hF0
  calc ∫ g, F g ∂μ = ((∫ g, F g ∂μ) ^ (p / s)) ^ (s / p) := by
        rw [← Real.rpow_mul hEF0, show p / s * (s / p) = 1 by field_simp, Real.rpow_one]
    _ ≤ (gaussMomentRoot p ^ p * ∑ i, ‖b i‖ ^ p) ^ (s / p) :=
        Real.rpow_le_rpow (by positivity) (hJ.trans_eq hEP) (by positivity)
    _ = _ := by
        rw [Real.mul_rpow (by positivity) hS, ← Real.rpow_mul hγ, Real.mul_rpow hγ
          (by positivity), ← Real.rpow_mul hS]
        congr 2
        · field_simp
        · ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
