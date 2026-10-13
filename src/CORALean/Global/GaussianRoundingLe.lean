import CORALean.Global.GaussianNormMomentLe

/-!
# Gaussian rounding: a pointwise ratio bound gives a bound on the norms

The rounding step of [1, Thm. 15 (accuracy)]. If `Σₖ |⟨aₖ, g⟩| ≤ r (Σᵢ |⟨bᵢ, g⟩|^p)^{1/p}` for
every `g`, then `γ₁ Σₖ ‖aₖ‖ ≤ r γ_p (Σᵢ ‖bᵢ‖^p)^{1/p}`, for `p ≥ 1` and `γ_k` the constant of
Eq. 31: take expectations at a standard Gaussian `g`. On the left
`E|⟨aₖ, g⟩| = γ₁ ‖aₖ‖`; on the right Jensen's inequality for `t ↦ t^p` moves the expectation
inside the root, where `E|⟨bᵢ, g⟩|^p = γ_p^p ‖bᵢ‖^p` (`gaussian_norm_moment_le`).

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
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `|⟨a, g⟩|^k` is integrable under the standard Gaussian. -/
theorem aux_integrable_abs_inner_rpow (a : E) {k : ℝ} (hk : 0 < k) :
    Integrable (fun g => |⟪a, g⟫| ^ k) (stdGaussian E) := by
  have h := (IsGaussian.memLp_dual (stdGaussian E) (innerSL ℝ a) (ENNReal.ofReal k)
    ENNReal.ofReal_ne_top).integrable_norm_rpow'
  simp only [ENNReal.toReal_ofReal hk.le, Real.norm_eq_abs, innerSL_apply_apply] at h
  exact h


-- =======================================  MAIN THEOREM  ======================================= --

theorem gaussian_rounding_le {s l : ℕ} (a : Fin s → E) (b : Fin l → E) {p r : ℝ} (hp : 1 ≤ p)
    (hr : 0 ≤ r)
    (h : ∀ g : E, ∑ k, |⟪a k, g⟫| ≤ r * (∑ i, |⟪b i, g⟫| ^ p) ^ (1 / p)) :
    gaussMomentRoot 1 * ∑ k, ‖a k‖ ≤
      r * (gaussMomentRoot p * (∑ i, ‖b i‖ ^ p) ^ (1 / p)) := by -- --- PROOF ---
  set μ := stdGaussian E
  set F : E → ℝ := fun g => (∑ i, |⟪b i, g⟫| ^ p) ^ (1 / p)
  obtain ⟨hFi, hEF⟩ := gaussian_norm_moment_le b zero_lt_one hp
  simp only [Real.rpow_one] at hFi hEF
  -- the left side in expectation
  have hL : gaussMomentRoot 1 * ∑ k, ‖a k‖ = ∫ g, ∑ k, |⟪a k, g⟫| ∂μ := by
    rw [integral_finsetSum _ fun k _ => by
      simpa using aux_integrable_abs_inner_rpow (a k) zero_lt_one]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := integral_abs_inner_rpow_stdGaussian (a k) zero_lt_one
    simp only [Real.rpow_one] at this
    rw [this, mul_comm]
  -- the pointwise bound in expectation
  rw [hL]
  calc ∫ g, ∑ k, |⟪a k, g⟫| ∂μ ≤ ∫ g, r * F g ∂μ :=
        integral_mono_of_nonneg (ae_of_all _ fun g => Finset.sum_nonneg fun k _ => abs_nonneg _)
          (hFi.const_mul r) (ae_of_all _ h)
    _ = r * ∫ g, F g ∂μ := integral_const_mul r _
    _ ≤ _ := mul_le_mul_of_nonneg_left hEF hr

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
