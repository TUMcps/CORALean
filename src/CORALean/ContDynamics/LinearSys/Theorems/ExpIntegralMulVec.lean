import CORALean.ContDynamics.LinearSys.Theorems.VariationOfConstants
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntegral

/-!
# The integrated exponential, applied to a vector, is the integral

`MatExp.expIntegral` is a series; this is what makes it the integral it is
named for. Only ever against a vector: `Matrix` has no metrizable-space instance
for Bochner integration to use, so `∫ e^{Aσ} dσ` does not exist as a matrix
here, while `∫ (e^{Aσ} v) dσ` exists perfectly well in `Vec`.

The exchange is dominated convergence over the partial sums, dominated by the
constant `e^{‖A‖t}‖v‖`. Termwise `∫₀ᵗ σⁱ/i! dσ = t^{i+1}/(i+1)!`, which is
where the shifted factorial in `expIntegral` comes from.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace MeasureTheory Filter Topology

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Applying a fixed vector, as a continuous linear map on matrices. -/
noncomputable def aux_mulVecR (v : Vec ℝ n) : Mat ℝ n n →L[ℝ] Vec ℝ n := mulVecL.flip v

theorem aux_mulVecR_apply (v : Vec ℝ n) (M : Mat ℝ n n) : aux_mulVecR v M = M *ᵥ v := rfl

/-- `‖A^i v‖ ≤ ‖A‖^i ‖v‖`, the `i = 0` case included, where the power is the
identity rather than something the operator norm bounds. -/
theorem aux_norm_pow_mulVec (A : Mat ℝ n n) (v : Vec ℝ n) (i : ℕ) :
    ‖A ^ i *ᵥ v‖ ≤ ‖A‖ ^ i * ‖v‖ := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · exact le_trans (Matrix.linfty_opNorm_mulVec _ _)
      (mul_le_mul_of_nonneg_right (norm_pow_le' A hi) (norm_nonneg _))

-- `ContinuousLinearMap.map_tsum` moves a `Mat ℝ n n` series under an application
set_option maxHeartbeats 400000 in
/-- The exponential series carried through to a vector. -/
theorem aux_exp_mulVec_tsum (A : Mat ℝ n n) (v : Vec ℝ n) (σ : ℝ) :
    exp (σ • A) *ᵥ v = ∑' i : ℕ, (((Nat.factorial i : ℝ))⁻¹ * σ ^ i) • (A ^ i *ᵥ v) := by
  rw [← aux_mulVecR_apply v, exp_smul_tsum A σ,
    ContinuousLinearMap.map_tsum (aux_mulVecR v) (summable_exp_smul A σ)]
  exact tsum_congr fun i => by rw [aux_mulVecR_apply, Matrix.smul_mulVec]

-- a `calc` over the `linftyOp` norm, whose instances are local to this file
set_option maxHeartbeats 400000 in
/-- Applying a vector only shrinks the terms, by `‖A^i v‖ ≤ ‖A^i‖ ‖v‖`, so
summability of a matrix series carries to it. -/
theorem aux_summable_smul_mulVec {c : ℕ → ℝ} (A : Mat ℝ n n) (v : Vec ℝ n)
    (h : Summable (fun i : ℕ => ‖c i • A ^ i‖)) :
    Summable (fun i : ℕ => c i • (A ^ i *ᵥ v)) := by -- --- PROOF ---
  refine Summable.of_norm_bounded (g := fun i : ℕ => ‖v‖ * ‖c i • A ^ i‖)
    (h.mul_left _) fun i => ?_
  rw [norm_smul, norm_smul]
  calc ‖c i‖ * ‖A ^ i *ᵥ v‖
      ≤ ‖c i‖ * (‖A ^ i‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left (Matrix.linfty_opNorm_mulVec _ _) (norm_nonneg _)
    _ = ‖v‖ * (‖c i‖ * ‖A ^ i‖) := by ring

-- `norm_expSeries_summable'` is elaborated at the four local `Matrix.linftyOp*` instances
set_option maxHeartbeats 400000 in
/-- Each order of the exponential series, applied to a vector, is summable. -/
theorem aux_summable_exp_mulVec (A : Mat ℝ n n) (v : Vec ℝ n) (σ : ℝ) :
    Summable (fun i : ℕ => (((Nat.factorial i : ℝ))⁻¹ * σ ^ i) • (A ^ i *ᵥ v)) := by
  refine aux_summable_smul_mulVec A v ?_
  refine (norm_expSeries_summable' (𝕂 := ℝ) (σ • A)).congr fun i => ?_
  rw [smul_pow, smul_smul]

-- the same instance search, one order higher
set_option maxHeartbeats 400000 in
/-- The same with the extra order integration adds. -/
theorem aux_summable_expIntegral_mulVec (A : Mat ℝ n n) (v : Vec ℝ n) (t : ℝ) :
    Summable (fun i : ℕ =>
      (((Nat.factorial (i + 1) : ℝ))⁻¹ * t ^ (i + 1)) • (A ^ i *ᵥ v)) :=
  aux_summable_smul_mulVec A v (MatExp.summable_norm_expIntegral A t)

/-- Each partial sum of the exponential series is continuous in the time. -/
theorem aux_continuous_expPartial (A : Mat ℝ n n) (v : Vec ℝ n) (N : ℕ) :
    Continuous fun σ : ℝ =>
      ∑ i ∈ Finset.range N, (((Nat.factorial i : ℝ))⁻¹ * σ ^ i) • (A ^ i *ᵥ v) :=
  continuous_finsetSum _ fun i _ =>
    ((continuous_const.mul (continuous_pow i)).smul continuous_const)


-- =======================================  MAIN THEOREM  ======================================= --

-- dominated convergence with its bound proved inline, over the same norm instances
set_option maxHeartbeats 1000000 in
/-- `expIntegral` is what its name says, once a vector is supplied. -/
theorem MatExp.expIntegral_mulVec (A : Mat ℝ n n) (v : Vec ℝ n) {t : ℝ} (ht : 0 ≤ t) :
    MatExp.expIntegral A t *ᵥ v = ∫ σ in (0:ℝ)..t, exp (σ • A) *ᵥ v := by -- --- PROOF ---
  have hseries : MatExp.expIntegral A t *ᵥ v
      = ∑' i : ℕ, (((Nat.factorial (i + 1) : ℝ))⁻¹ * t ^ (i + 1)) • (A ^ i *ᵥ v) := by
    rw [← aux_mulVecR_apply v, MatExp.expIntegral,
      ContinuousLinearMap.map_tsum (aux_mulVecR v) (MatExp.summable_expIntegral A t)]
    exact tsum_congr fun i => by rw [aux_mulVecR_apply, Matrix.smul_mulVec]
  -- each partial sum is the integral of the truncated series
  have hpartial : ∀ N : ℕ, (∑ i ∈ Finset.range N,
      (((Nat.factorial (i + 1) : ℝ))⁻¹ * t ^ (i + 1)) • (A ^ i *ᵥ v))
      = ∫ σ in (0:ℝ)..t, ∑ i ∈ Finset.range N,
          (((Nat.factorial i : ℝ))⁻¹ * σ ^ i) • (A ^ i *ᵥ v) := by
    intro N
    have hint : ∀ i ∈ Finset.range N, IntervalIntegrable
        (fun σ : ℝ => (((Nat.factorial i : ℝ))⁻¹ * σ ^ i) • (A ^ i *ᵥ v)) volume 0 t :=
      fun i _ => ((continuous_const.mul (continuous_pow i)).smul
        continuous_const).intervalIntegrable 0 t
    rw [intervalIntegral.integral_finsetSum hint]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_smul_const, intervalIntegral.integral_const_mul,
      integral_pow]
    congr 1
    have hfac : (0:ℝ) < (Nat.factorial i : ℝ) := by exact_mod_cast Nat.factorial_pos i
    have hi1 : ((i : ℝ) + 1) ≠ 0 := by positivity
    rw [Nat.factorial_succ, zero_pow (Nat.succ_ne_zero i)]
    push_cast
    field_simp
    ring
  -- the truncated series converges to the exponential, dominated by a constant
  have hdom : Tendsto (fun N : ℕ => ∫ σ in (0:ℝ)..t, ∑ i ∈ Finset.range N,
      (((Nat.factorial i : ℝ))⁻¹ * σ ^ i) • (A ^ i *ᵥ v)) atTop
      (𝓝 (∫ σ in (0:ℝ)..t, exp (σ • A) *ᵥ v)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => Real.exp (‖A‖ * t) * ‖v‖)
      (Filter.Eventually.of_forall fun N =>
        (aux_continuous_expPartial A v N).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun N =>
        Filter.Eventually.of_forall fun σ hσ => ?_)
      intervalIntegrable_const
      (Filter.Eventually.of_forall fun σ _ => ?_)
    -- the dominating bound: every partial sum stays under `e^{‖A‖t}‖v‖` on the step
    · rw [Set.uIoc_of_le ht] at hσ
      have hσ0 : (0:ℝ) ≤ σ := hσ.1.le
      calc ‖∑ i ∈ Finset.range N, (((Nat.factorial i : ℝ))⁻¹ * σ ^ i) • (A ^ i *ᵥ v)‖
          ≤ ∑ i ∈ Finset.range N, ‖(((Nat.factorial i : ℝ))⁻¹ * σ ^ i) • (A ^ i *ᵥ v)‖ :=
            norm_sum_le _ _
        -- the vector comes out of every term, leaving the scalar exponential series
        _ ≤ ∑ i ∈ Finset.range N, (‖A‖ * σ) ^ i / (Nat.factorial i : ℝ) * ‖v‖ := by
            refine Finset.sum_le_sum fun i _ => ?_
            have hnn : (0:ℝ) ≤ ((Nat.factorial i : ℝ))⁻¹ * σ ^ i :=
              mul_nonneg (by positivity) (pow_nonneg hσ0 i)
            rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_inv, abs_pow,
              abs_of_pos (by exact_mod_cast Nat.factorial_pos i : (0:ℝ) < _),
              abs_of_nonneg hσ0]
            calc ((Nat.factorial i : ℝ))⁻¹ * σ ^ i * ‖A ^ i *ᵥ v‖
                ≤ ((Nat.factorial i : ℝ))⁻¹ * σ ^ i * (‖A‖ ^ i * ‖v‖) :=
                  mul_le_mul_of_nonneg_left (aux_norm_pow_mulVec A v i) hnn
              _ = (‖A‖ * σ) ^ i / (Nat.factorial i : ℝ) * ‖v‖ := by
                  rw [mul_pow]; ring
        _ = (∑ i ∈ Finset.range N, (‖A‖ * σ) ^ i / (Nat.factorial i : ℝ)) * ‖v‖ :=
            (Finset.sum_mul _ _ _).symm
        _ ≤ Real.exp (‖A‖ * t) * ‖v‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            refine le_trans (Real.sum_le_exp_of_nonneg
              (mul_nonneg (norm_nonneg A) hσ0) N) ?_
            exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hσ.2 (norm_nonneg A))
    -- and the pointwise limit is the exponential applied to the vector
    · have h := (aux_summable_exp_mulVec A v σ).hasSum.tendsto_sum_nat
      rwa [← aux_exp_mulVec_tsum A v σ] at h
  rw [hseries]
  exact ((aux_summable_expIntegral_mulVec A v t).hasSum_iff_tendsto_nat.mpr
    (hdom.congr fun N => (hpartial N).symm)).tsum_eq

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
