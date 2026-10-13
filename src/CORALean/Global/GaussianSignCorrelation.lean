import CORALean.Global.GaussianAbsMoment
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# The correlation of a Gaussian projection with the sign of another

The sign rounding of [1, Thm. 17]: for a standard Gaussian `g`, the product
`⟨y, g⟩ sign⟨c, g⟩` is integrable and `E[⟨y, g⟩ sign⟨c, g⟩] = γ₁ ⟨y, c⟩ / ‖c‖`,
`γ₁ = √(2/π)` the constant of Eq. 31 (both sides `0` at `c = 0`). Split
`y = (⟨y, c⟩ / ‖c‖²) c + y⊥` with `y⊥ ⟂ c`. The first part gives
`(⟨y, c⟩ / ‖c‖²) E|⟨c, g⟩| = (⟨y, c⟩ / ‖c‖²) γ₁ ‖c‖`
(`integral_abs_inner_rpow_stdGaussian`). The second has expectation `0`: the reflection in
`y⊥ᗮ` fixes `c`, negates `y⊥` and preserves the standard Gaussian, so it negates the integral.

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

theorem aux_gsc_measurable_sign :
    Measurable fun x : ℝ => (SignType.sign x : ℝ) := by -- --- PROOF ---
  have : (fun x : ℝ => (SignType.sign x : ℝ)) =
      fun x => if 0 < x then 1 else if x < 0 then -1 else 0 := by
    funext x
    rw [sign_apply]
    split_ifs <;> simp
  rw [this]
  exact Measurable.ite measurableSet_Ioi measurable_const
    (Measurable.ite measurableSet_Iio measurable_const measurable_const)

/-- `⟨y, g⟩ sign⟨c, g⟩` is integrable: it is at most `|⟨y, g⟩|`. -/
theorem aux_gsc_integrable (y c : E) :
    Integrable (fun g => ⟪y, g⟫ * (SignType.sign ⟪c, g⟫ : ℝ)) (stdGaussian E) := by -- --- PROOF ---
  refine (IsGaussian.integrable_dual (stdGaussian E) (innerSL ℝ y)).norm.mono' ?_
    (ae_of_all _ fun g => ?_)
  · exact ((continuous_const.inner continuous_id).aestronglyMeasurable).mul
      (aux_gsc_measurable_sign.comp
        (continuous_const.inner continuous_id).measurable).aestronglyMeasurable
  · simp only [norm_mul, Real.norm_eq_abs, innerSL_apply_apply]
    refine mul_le_of_le_one_right (abs_nonneg _) ?_
    rcases lt_trichotomy ⟪c, g⟫ 0 with h | h | h <;> simp [h]


-- =======================================  MAIN THEOREM  ======================================= --

theorem integral_inner_mul_sign_inner_stdGaussian (y c : E) :
    Integrable (fun g => ⟪y, g⟫ * (SignType.sign ⟪c, g⟫ : ℝ)) (stdGaussian E) ∧
      ∫ g, ⟪y, g⟫ * (SignType.sign ⟪c, g⟫ : ℝ) ∂(stdGaussian E) =
        gaussMomentRoot 1 * ⟪y, c⟫ / ‖c‖ := by -- --- PROOF ---
  refine ⟨aux_gsc_integrable y c, ?_⟩
  set μ := stdGaussian E
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have hc0 : 0 < ‖c‖ := norm_pos_iff.mpr hc
  set t : ℝ := ⟪y, c⟫ / ‖c‖ ^ 2
  set y' : E := y - t • c
  have hy'c : ⟪c, y'⟫ = 0 := by
    simp only [y', t, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq,
      real_inner_comm c y]
    field_simp
    ring
  -- the reflection fixing `c` and negating `y'`
  set K : Submodule ℝ E := (ℝ ∙ y')ᗮ
  set R := K.reflection
  have hcK : c ∈ K := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    rw [real_inner_comm]
    exact hy'c
  have hRc : ∀ g, ⟪c, R g⟫ = ⟪c, g⟫ := fun g => by
    conv_lhs => rw [← K.reflection_mem_subspace_eq_self hcK]
    exact R.inner_map_map c g
  have hRy : ∀ g, ⟪y', R g⟫ = -⟪y', g⟫ := fun g => by
    have h := R.inner_map_map y' (R g)
    rw [K.reflection_reflection, Submodule.reflection_orthogonalComplement_singleton_eq_neg,
      inner_neg_left] at h
    linarith
  have hmap : μ.map R = μ := stdGaussian_map R
  -- the orthogonal part has expectation `0`
  have h0 : ∫ g, ⟪y', g⟫ * (SignType.sign ⟪c, g⟫ : ℝ) ∂μ = 0 := by
    have h : ∫ g, ⟪y', g⟫ * (SignType.sign ⟪c, g⟫ : ℝ) ∂(μ.map R) =
        ∫ g, ⟪y', R g⟫ * (SignType.sign ⟪c, R g⟫ : ℝ) ∂μ :=
      integral_map R.continuous.aemeasurable (by
        rw [hmap]; exact (aux_gsc_integrable y' c).aestronglyMeasurable)
    have h' : ∫ g, ⟪y', R g⟫ * (SignType.sign ⟪c, R g⟫ : ℝ) ∂μ =
        -∫ g, ⟪y', g⟫ * (SignType.sign ⟪c, g⟫ : ℝ) ∂μ := by
      simp only [hRc, hRy, neg_mul]
      exact integral_neg _
    rw [hmap, h'] at h
    linarith
  -- the parallel part is `t E|⟨c, g⟩|`
  have h1 : ∫ g, ⟪c, g⟫ * (SignType.sign ⟪c, g⟫ : ℝ) ∂μ = gaussMomentRoot 1 * ‖c‖ := by
    have := integral_abs_inner_rpow_stdGaussian c (E := E) zero_lt_one
    simp only [Real.rpow_one] at this
    simp only [self_mul_sign]
    rw [this, mul_comm]
  have hsplit : ∀ g, ⟪y, g⟫ * (SignType.sign ⟪c, g⟫ : ℝ) =
      t * (⟪c, g⟫ * (SignType.sign ⟪c, g⟫ : ℝ)) + ⟪y', g⟫ * (SignType.sign ⟪c, g⟫ : ℝ) :=
    fun g => by
      simp only [y', inner_sub_left, inner_smul_left, RCLike.conj_to_real]
      ring
  simp only [hsplit]
  rw [integral_add ((aux_gsc_integrable c c).const_mul t) (aux_gsc_integrable y' c),
    integral_const_mul, h1, h0, add_zero]
  simp only [t]
  field_simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
