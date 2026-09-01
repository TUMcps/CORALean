import CORALean.ContDynamics.LinearSys.Operations
import CORALean.ContDynamics.LinearSys.Theorems.VariationOfConstants
import CORALean.ContDynamics.LinearSys.Theorems.WeightedIntegral
import CORALean.ContDynamics.LinearSys.MatExp.API

/-!
# `inputSolution` contains everything the input can contribute over a step

Althoff's Thm. 3.1. Substituting `τ = r - s` turns `∫₀ʳ e^{A(r-s)}u(s)ds` into
`∫₀ʳ e^{Aτ}u(r-τ)dτ`, and the exponential splits into its first `η+1` orders
plus a remainder — a *finite* sum, so linearity of the integral does the whole
split and no series has to be exchanged with an integral.

Each exact order comes out as `Aⁱ/i!` applied to `∫₀ʳ τⁱ u(r-τ)dτ`, the matrix
leaving the integral before `integral_pow_smul_mem` is used, so convexity is
asked only of `U`. The remainder cannot do that — `R(τ)` varies with `τ` — so
there the convex closed set is the product `E(r)·r·U`, which is why that
hypothesis is about the operation's result rather than its argument.

`0 ∈ U` is not needed: this is the enclosure at `r`, and Prop. 3.3 is what would
extend it to all of `[0,r]`.
-/

-- Authors:       Tobias Ladner
-- Written:       19-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar NormedSpace MeasureTheory Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, OuterContSet (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]

omit [∀ n, OuterContSet (S n) (Vec ℝ n)] in
/-- A matrix applied to a scaled point is the scaled matrix applied to it, which
is how a constant in front of an integral is absorbed into the operation. -/
theorem aux_smul_mtimes_mem {M : Mat ℝ n n} {c : ℝ} {U : S n} {y : Vec ℝ n}
    (hy : y ∈ construct U) :
    M *ᵥ (c • y) ∈ construct (Mtimes.mtimes (c • M) U) := by
  have hM : M *ᵥ (c • y) = (c • M) *ᵥ y := by
    rw [Matrix.mulVec_smul, Matrix.smul_mulVec]
  rw [hM]
  refine Mtimes.mtimes_outer _ _ ?_
  simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
  exact Set.mem_image_of_mem _ hy

/-- The Taylor part, by induction on the order: `plus` absorbs one term at a
time, exactly as the operation builds it. -/
theorem LinearSys.aux_inputTaylorSum_outer (sys : LinearSys 𝕋 n) (r : ℝ) (U : S n)
    (x : ℕ → Vec ℝ n) : ∀ (η : ℕ),
    (∀ i, i ≤ η → x i ∈ construct (Mtimes.mtimes (sys.inputTerm r i) U)) →
    (∑ i ∈ Finset.range (η + 1), x i) ∈ construct (sys.inputTaylorSum r U η)
  | 0, hx => by
    rw [Finset.sum_range_one]
    exact hx 0 (le_refl 0)
  | m + 1, hx => by
    rw [Finset.sum_range_succ]
    exact Plus.plus_outer _ _ (Set.add_mem_add
      (sys.aux_inputTaylorSum_outer r U x m fun i hi => hx i (le_trans hi (Nat.le_succ m)))
      (hx (m + 1) (le_refl _)))

/-- The exponential's first `η+1` orders, applied to a vector, with the powers
of `τ` pulled out as scalars. -/
theorem aux_expTaylor_smul_mulVec (A : Mat ℝ n n) (η : ℕ) (τ : ℝ) (v : Vec ℝ n) :
    MatExp.expTaylor (τ • A) η *ᵥ v
      = ∑ i ∈ Finset.range (η + 1), ((Nat.factorial i : ℝ)⁻¹ * τ ^ i) • (A ^ i *ᵥ v) := by
  rw [MatExp.expTaylor, Matrix.sum_mulVec]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_pow, Matrix.smul_mulVec, Matrix.smul_mulVec, mul_smul]

/-- Every entry of the remainder is within the step's bound, uniformly over the
step: the bound grows with `‖τ • A‖`, so the value at `r` covers all of `[0,r]`. -/
theorem aux_remainder_entry_le (A : Mat ℝ n n) {r τ : ℝ} (η : ℕ) (hr : 0 < r)
    (hτ0 : 0 ≤ τ) (hτr : τ ≤ r) (hε : ‖r • A‖ / ((η : ℝ) + 2) < 1) (j k : Fin n) :
    |(exp (τ • A) - MatExp.expTaylor (τ • A) η) j k|
      ≤ MatExp.expRemainderBound (r • A) η := by
  have hnorm : ‖τ • A‖ ≤ ‖r • A‖ := by
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hτ0,
      abs_of_nonneg hr.le]
    exact mul_le_mul_of_nonneg_right hτr (norm_nonneg A)
  have hετ : ‖τ • A‖ / ((η : ℝ) + 2) < 1 := by
    have h2 : (0:ℝ) < (η : ℝ) + 2 := by positivity
    calc ‖τ • A‖ / ((η : ℝ) + 2) ≤ ‖r • A‖ / ((η : ℝ) + 2) := by gcongr
      _ < 1 := hε
  calc |(exp (τ • A) - MatExp.expTaylor (τ • A) η) j k|
      ≤ ‖exp (τ • A) - MatExp.expTaylor (τ • A) η‖ := abs_entry_le_norm _ j k
    _ ≤ MatExp.expRemainderBound (τ • A) η := norm_exp_sub_expTaylor_le _ η hετ
    _ ≤ MatExp.expRemainderBound (r • A) η :=
        MatExp.expRemainderBound_mono η hnorm hε

/-- The exponential and its truncation are continuous in the time, so their
difference is too and the remainder integrand is measurable. -/
theorem aux_continuous_expDiff (A : Mat ℝ n n) (η : ℕ) :
    Continuous fun τ : ℝ => exp (τ • A) - MatExp.expTaylor (τ • A) η := by
  have hsmul : Continuous fun τ : ℝ => τ • A := continuous_id.smul continuous_const
  refine (exp_continuous.comp hsmul).sub ?_
  simp only [MatExp.expTaylor]
  refine continuous_finsetSum _ fun i _ => ?_
  exact (continuous_const : Continuous fun _ : ℝ => ((Nat.factorial i : ℝ)⁻¹)).smul (hsmul.pow i)

set_option maxHeartbeats 1000000 in
theorem LinearSys.inputSolution_outer [Mtimes ℐ S]
    (sys : LinearSys 𝕋 n)
    {r : ℝ} (hr : 0 < r) (η : ℕ)
    (hε : ‖r • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1) {U : S n}
    (hconv : Convex ℝ (construct U)) (hclosed : IsClosed (construct U))
    (hbdd : Bornology.IsBounded (construct U))
    (hRconv : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r η) U)))
    (hRclosed : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r η) U)))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r η) U)))
    {u : ℝ → Vec ℝ n}
    (hu : ∀ τ ∈ Set.Ioc (0:ℝ) r, u (r - τ) ∈ construct U)
    (hmeas : AEStronglyMeasurable (fun τ => u (r - τ)) (volume.restrict (Set.Ioc 0 r))) :
    (∫ s in (0:ℝ)..r, exp ((r - s) • toRealMat sys.A) *ᵥ u s)
      ∈ construct (sys.inputSolution r η U) := by
  set A := toRealMat sys.A with hA
  set g : ℝ → Vec ℝ n := fun τ => u (r - τ) with hg
  obtain ⟨C, hC⟩ := hbdd.exists_norm_le
  -- integrability, from boundedness and measurability, once for every piece
  have hint : ∀ (F : ℝ → Vec ℝ n) (K : ℝ),
      AEStronglyMeasurable F (volume.restrict (Set.Ioc 0 r)) →
      (∀ τ ∈ Set.Ioc (0:ℝ) r, ‖F τ‖ ≤ K) → IntervalIntegrable F volume 0 r := by
    intro F K hFm hFb
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hr.le]
    exact ⟨hFm, HasFiniteIntegral.restrict_of_bounded (C := K) measure_Ioc_lt_top
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall hFb))⟩
  have hgbd : ∀ τ ∈ Set.Ioc (0:ℝ) r, ‖g τ‖ ≤ C := fun τ hτ => hC _ (hu τ hτ)
  -- the substitution `τ = r - s`
  have hsub : (∫ s in (0:ℝ)..r, exp ((r - s) • A) *ᵥ u s)
      = ∫ τ in (0:ℝ)..r, exp (τ • A) *ᵥ g τ := by
    have h := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := r)
      (f := fun τ => exp (τ • A) *ᵥ g τ) r
    simp only [hg, sub_sub_cancel, sub_self, sub_zero] at h
    exact h
  -- the integrand, split into the exact orders and the remainder
  have hsplit : ∀ τ : ℝ, exp (τ • A) *ᵥ g τ
      = (∑ i ∈ Finset.range (η + 1), ((Nat.factorial i : ℝ)⁻¹ * τ ^ i) • (A ^ i *ᵥ g τ))
        + (exp (τ • A) - MatExp.expTaylor (τ • A) η) *ᵥ g τ := by
    intro τ
    rw [← aux_expTaylor_smul_mulVec A η τ (g τ), Matrix.sub_mulVec]
    abel
  -- each exact order lands in its own term of the operation
  have hterm : ∀ i, i ≤ η →
      (∫ τ in (0:ℝ)..r, ((Nat.factorial i : ℝ)⁻¹ * τ ^ i) • (A ^ i *ᵥ g τ))
        ∈ construct (Mtimes.mtimes (sys.inputTerm r i) U) := by
    intro i _
    have hgi : IntervalIntegrable (fun τ => τ ^ i • g τ) volume 0 r :=
      hint _ (r ^ i * C) ((continuous_pow i).aestronglyMeasurable.smul hmeas)
        (fun τ hτ => by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hτ.1.le i)]
          exact mul_le_mul (pow_le_pow_left₀ hτ.1.le hτ.2 i) (hgbd τ hτ) (norm_nonneg _)
            (pow_nonneg hr.le i))
    have hy : (∫ τ in (0:ℝ)..r, τ ^ i • g τ) ∈ (r ^ (i + 1) / ((i : ℝ) + 1)) • construct U :=
      integral_pow_smul_mem hconv hclosed hbdd hr i hmeas hu
    obtain ⟨z, hz, hzeq⟩ := hy
    have hpull : (∫ τ in (0:ℝ)..r, ((Nat.factorial i : ℝ)⁻¹ * τ ^ i) • (A ^ i *ᵥ g τ))
        = ((Nat.factorial i : ℝ)⁻¹) • (A ^ i *ᵥ ∫ τ in (0:ℝ)..r, τ ^ i • g τ) := by
      have hfun : ∀ τ : ℝ, ((Nat.factorial i : ℝ)⁻¹ * τ ^ i) • (A ^ i *ᵥ g τ)
          = ((Nat.factorial i : ℝ)⁻¹) • ((mulVecL (A ^ i)) (τ ^ i • g τ)) := by
        intro τ
        rw [map_smul, mul_smul]
        rfl
      have hclm : (∫ τ in (0:ℝ)..r, (mulVecL (A ^ i)) (τ ^ i • g τ))
          = (mulVecL (A ^ i)) (∫ τ in (0:ℝ)..r, τ ^ i • g τ) :=
        ContinuousLinearMap.intervalIntegral_comp_comm _ hgi
      simp only [hfun]
      rw [intervalIntegral.integral_smul, hclm]
      rfl
    rw [hpull, ← hzeq]
    have hcomb : ((Nat.factorial i : ℝ)⁻¹) • (A ^ i *ᵥ ((r ^ (i + 1) / ((i : ℝ) + 1)) • z))
        = (sys.inputTerm r i) *ᵥ z := by
      rw [Matrix.mulVec_smul, smul_smul, LinearSys.inputTerm, Matrix.smul_mulVec]
      congr 1
      rw [Nat.factorial_succ]
      have h1 : ((i : ℝ) + 1) ≠ 0 := by positivity
      have h2 : (Nat.factorial i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
      push_cast
      field_simp
    rw [hcomb]
    refine Mtimes.mtimes_outer _ _ ?_
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact Set.mem_image_of_mem _ hz
  -- the remainder: `R(τ)` varies, so the convex closed set is the product itself
  -- `Matrix` blocks instance search, so the remainder's measurability is taken
  -- one entry at a time, where everything is a real-valued product
  have hgk : ∀ k, AEStronglyMeasurable (fun τ => g τ k) (volume.restrict (Set.Ioc 0 r)) := by
    intro k
    rw [aestronglyMeasurable_iff_aemeasurable]
    exact (aemeasurable_pi_iff.mp (aestronglyMeasurable_iff_aemeasurable.mp hmeas)) k
  have hRmeas : AEStronglyMeasurable
      (fun τ => (exp (τ • A) - MatExp.expTaylor (τ • A) η) *ᵥ g τ)
      (volume.restrict (Set.Ioc 0 r)) := by
    rw [aestronglyMeasurable_iff_aemeasurable]
    refine aemeasurable_pi_iff.mpr fun j => ?_
    have hj : ∀ τ : ℝ, ((exp (τ • A) - MatExp.expTaylor (τ • A) η) *ᵥ g τ) j
        = ∑ k, (exp (τ • A) - MatExp.expTaylor (τ • A) η) j k * g τ k := fun _ => rfl
    simp only [hj]
    rw [← aestronglyMeasurable_iff_aemeasurable]
    -- `Finset.aestronglyMeasurable_sum` sums functions, the goal sums values
    have heq : (∑ k : Fin n, (fun τ : ℝ =>
          (exp (τ • A) - MatExp.expTaylor (τ • A) η) j k * g τ k))
        = fun τ : ℝ => ∑ k, (exp (τ • A) - MatExp.expTaylor (τ • A) η) j k * g τ k := by
      funext τ
      simp only [Finset.sum_apply]
    rw [← heq]
    exact Finset.aestronglyMeasurable_sum _ fun k _ =>
      (((aux_continuous_expDiff A η).matrix_elem j k).aestronglyMeasurable).mul (hgk k)
  have hpt : ∀ τ ∈ Set.Ioc (0:ℝ) r,
      r • ((exp (τ • A) - MatExp.expTaylor (τ • A) η) *ᵥ g τ)
        ∈ construct (Mtimes.mtimes (𝕄 := ℐ)
        (MatExp.inputRemainder A r η) U) := by
    intro τ hτ
    have hM : (r • (exp (τ • A) - MatExp.expTaylor (τ • A) η))
        ∈ (MatExp.inputRemainder A r η).construct := by
      refine Interval.mem_mat_iff.mpr fun j k => ?_
      have hb := aux_remainder_entry_le A η hr hτ.1.le hτ.2 hε j k
      rw [abs_le] at hb
      refine ⟨?_, ?_⟩
      · show -(r * _) ≤ r * _
        nlinarith [hb.1, hr.le]
      · show r * _ ≤ r * _
        nlinarith [hb.2, hr.le]
    rw [← Matrix.smul_mulVec]
    exact Mtimes.mtimes_outer _ _ (Set.mem_biUnion hM (Set.mem_image_of_mem _ (hu τ hτ)))
  have hrem : (∫ τ in (0:ℝ)..r, (exp (τ • A) - MatExp.expTaylor (τ • A) η) *ᵥ g τ)
      ∈ construct (Mtimes.mtimes (𝕄 := ℐ)
        (MatExp.inputRemainder A r η) U) := by
    have hI := integral_pow_smul_mem hRconv hRclosed hRbdd hr 0
      (f := fun τ => r • ((exp (τ • A) - MatExp.expTaylor (τ • A) η) *ᵥ g τ))
      (hmeas := hRmeas.fun_const_smul r) (hmem := hpt)
    simp only [pow_zero, one_smul, pow_one, Nat.cast_zero, zero_add, div_one,
      intervalIntegral.integral_smul] at hI
    obtain ⟨y, hy, hyeq⟩ := hI
    have hinj : y = ∫ τ in (0:ℝ)..r, (exp (τ • A) - MatExp.expTaylor (τ • A) η) *ᵥ g τ :=
      smul_right_injective _ hr.ne' hyeq
    rwa [← hinj]
  -- everything is integrable, so the split survives the integral
  have hRint : IntervalIntegrable
      (fun τ => (exp (τ • A) - MatExp.expTaylor (τ • A) η) *ᵥ g τ) volume 0 r := by
    obtain ⟨D, hD⟩ := (isCompact_Icc (a := (0:ℝ)) (b := r)).exists_bound_of_continuousOn
      (aux_continuous_expDiff A η).continuousOn
    refine hint _ (D * C) hRmeas fun τ hτ => ?_
    exact le_trans (Matrix.linfty_opNorm_mulVec _ _)
      (mul_le_mul (hD τ ⟨hτ.1.le, hτ.2⟩) (hgbd τ hτ) (norm_nonneg _)
        (le_trans (norm_nonneg _) (hD 0 ⟨le_refl 0, hr.le⟩)))
  have hTint : ∀ i ∈ Finset.range (η + 1), IntervalIntegrable
      (fun τ => ((Nat.factorial i : ℝ)⁻¹ * τ ^ i) • (A ^ i *ᵥ g τ)) volume 0 r := by
    intro i _
    refine hint _ ((Nat.factorial i : ℝ)⁻¹ * r ^ i * (‖A ^ i‖ * C)) ?_ fun τ hτ => ?_
    · exact (continuous_const.mul (continuous_pow i)).aestronglyMeasurable.smul
        ((mulVecL (A ^ i)).continuous.comp_aestronglyMeasurable hmeas)
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (by positivity) (pow_nonneg hτ.1.le i))]
      refine mul_le_mul ?_ (le_trans (Matrix.linfty_opNorm_mulVec _ _)
        (mul_le_mul_of_nonneg_left (hgbd τ hτ) (norm_nonneg _))) (norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hτ.1.le hτ.2 i) (by positivity)
  rw [hsub]
  simp only [hsplit]
  have hSint : IntervalIntegrable
      (fun τ => ∑ i ∈ Finset.range (η + 1), ((Nat.factorial i : ℝ)⁻¹ * τ ^ i) • (A ^ i *ᵥ g τ))
      volume 0 r := by
    have heq : (∑ i ∈ Finset.range (η + 1),
          (fun τ : ℝ => ((Nat.factorial i : ℝ)⁻¹ * τ ^ i) • (A ^ i *ᵥ g τ)))
        = fun τ : ℝ => ∑ i ∈ Finset.range (η + 1),
            ((Nat.factorial i : ℝ)⁻¹ * τ ^ i) • (A ^ i *ᵥ g τ) := by
      funext τ
      simp only [Finset.sum_apply]
    rw [← heq]
    exact IntervalIntegrable.sum _ hTint
  rw [intervalIntegral.integral_add hSint hRint,
    intervalIntegral.integral_finsetSum hTint]
  exact Plus.plus_outer _ _ (Set.add_mem_add
    (sys.aux_inputTaylorSum_outer r U _ η hterm) hrem)

end CORALean.Real
