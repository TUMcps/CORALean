module

public import CORALean.ContDynamics.LinParamSys.Operations.InputSolution
public import CORALean.ContDynamics.LinParamSys.Operations.InputTaylorSum
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ContinuousExpDiff
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpTaylorSmulMulVec
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalInputRemainder
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.RemainderEntryLe
public import CORALean.ContDynamics.LinearSys.Definitions.MulVecL
public import CORALean.ContDynamics.LinearSys.Theorems.WeightedIntegral
public import CORALean.ContSet.Interval.Real.Theorems.MatPowOuter
public import CORALean.ContSet.Interval.Real.Theorems.MemMat
public import CORALean.ContSet.Interval.Real.Theorems.NormLeAbsMax
public import CORALean.ContSet.Interval.Real.Theorems.SmulOuter

@[expose] public section

/-!
# `inputSolution` contains what the input contributes at every matrix of the set

`LinearSys.inputSolution_outer` at a matrix drawn from `construct sys.A`, which
is the whole difference: the run is `'constParam'`, so one member `A` is fixed
and the argument about the integral is the point one unchanged. What changes is
where each piece lands — every order is now an interval matrix, reached by
`matPow_outer` and `smul_outer` rather than by a singleton, and the tail goes
through the member's own remainder into the box's by
`intervalInputRemainder_contains`.

`hε` is stated at the box, checkable before a member is fixed; `hεA` is what it
gives at the member, which is what the entrywise bound needs.

The three hypotheses on the remainder product are asked of the product and not
of `U`, `R(τ)` varying with `τ`, exactly as in the point case.

`0 ∈ U` is not needed: this is the enclosure at `r`. The extension to all of
`[0, r]` is `inputSolution_timeInterval_outer`, and that is where it is paid.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet NormedSpace MeasureTheory Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes ℐ S]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The Taylor part, by induction on the order: `plus` absorbs one term at a
time, exactly as the operation builds it. -/
theorem LinParamSys.aux_inputTaylorSum_outer (sys : LinParamSys ℐ n) (r : ℝ) (U : S n)
    (x : ℕ → Vec ℝ n) : ∀ (η : ℕ),
    (∀ i, i ≤ η → x i ∈ construct (Mtimes.mtimes (𝕄 := ℐ) (sys.inputTerm r i) U)) →
    (∑ i ∈ Finset.range (η + 1), x i) ∈ construct (sys.inputTaylorSum r U η)
  | 0, hx => by
    rw [Finset.sum_range_one]
    exact hx 0 (le_refl 0)
  | m + 1, hx => by
    rw [Finset.sum_range_succ]
    exact Plus.plus_outer _ _ (Set.add_mem_add
      (sys.aux_inputTaylorSum_outer r U x m fun i hi => hx i (le_trans hi (Nat.le_succ m)))
      (hx (m + 1) (le_refl _)))


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinParamSys.inputSolution_outer (sys : LinParamSys ℐ n)
    {r : ℝ} (hr : 0 < r) (η : ℕ)
    (hε : ‖(Interval.smul r sys.A).absMax‖ / ((η : ℝ) + 2) < 1)
    {A : Mat ℝ n n} (hA : A ∈ construct sys.A) {U : S n}
    (hconv : Convex ℝ (construct U)) (hclosed : IsClosed (construct U))
    (hbdd : Bornology.IsBounded (construct U))
    -- the next three are asked of the product and not of `U`, `R(τ)` varying with `τ`
    (hRconv : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.intervalInputRemainder sys.A r η) U)))
    (hRclosed : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.intervalInputRemainder sys.A r η) U)))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.intervalInputRemainder sys.A r η) U)))
    {u : ℝ → Vec ℝ n}
    (hu : ∀ τ ∈ Set.Ioc (0:ℝ) r, u (r - τ) ∈ construct U)
    (hmeas : AEStronglyMeasurable (fun τ => u (r - τ)) (volume.restrict (Set.Ioc 0 r))) :
    (∫ s in (0:ℝ)..r, exp ((r - s) • A) *ᵥ u s)
      ∈ construct (sys.inputSolution r η U) := by -- --- PROOF ---
  -- the condition is checkable from the box; the member's own is what the tail needs
  have hnorm : ‖r • A‖ ≤ ‖(Interval.smul r sys.A).absMax‖ :=
    Interval.norm_le_absMax (Interval.smul_outer r sys.A hA)
  have hεA : ‖r • A‖ / ((η : ℝ) + 2) < 1 := lt_of_le_of_lt (by gcongr) hε
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
    rw [← MatExp.expTaylor_smul_mulVec A η τ (g τ), Matrix.sub_mulVec]
    abel
  -- each exact order lands in its own term of the operation
  have hterm : ∀ i, i ≤ η →
      (∫ τ in (0:ℝ)..r, ((Nat.factorial i : ℝ)⁻¹ * τ ^ i) • (A ^ i *ᵥ g τ))
        ∈ construct (Mtimes.mtimes (𝕄 := ℐ) (sys.inputTerm r i) U) := by
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
    -- the matrix leaves the integral, so convexity is asked only of `U`
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
    -- `Aⁱ/i!` against `r^(i+1)/(i+1)` is the member of `inputTerm r i` this run uses
    have hcomb : ((Nat.factorial i : ℝ)⁻¹) • (A ^ i *ᵥ ((r ^ (i + 1) / ((i : ℝ) + 1)) • z))
        = ((r ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)) • A ^ i) *ᵥ z := by
      rw [Matrix.mulVec_smul, smul_smul, Matrix.smul_mulVec]
      congr 1
      rw [Nat.factorial_succ]
      have h1 : ((i : ℝ) + 1) ≠ 0 := by positivity
      have h2 : (Nat.factorial i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
      push_cast
      field_simp
    rw [hcomb]
    exact Mtimes.mtimes_outer _ _ (Set.mem_biUnion
      (Interval.smul_outer _ _ (Interval.matPow_outer sys.A hA i))
      (Set.mem_image_of_mem _ hz))
  -- `Matrix` blocks instance search, so the remainder is measured one real entry at a time
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
      (((MatExp.continuous_expDiff A η).matrix_elem j k).aestronglyMeasurable).mul (hgk k)
  -- every entry of `r · R(τ)` lies in the member's remainder, and so in the box's
  have hpt : ∀ τ ∈ Set.Ioc (0:ℝ) r,
      r • ((exp (τ • A) - MatExp.expTaylor (τ • A) η) *ᵥ g τ)
        ∈ construct (Mtimes.mtimes (𝕄 := ℐ)
        (MatExp.intervalInputRemainder sys.A r η) U) := by
    intro τ hτ
    have hM : (r • (exp (τ • A) - MatExp.expTaylor (τ • A) η))
        ∈ (MatExp.intervalInputRemainder sys.A r η).construct := by
      refine MatExp.intervalInputRemainder_contains sys.A hr η hε hA ?_
      refine Interval.mem_mat_iff.mpr fun j k => ?_
      have hb := MatExp.remainder_entry_le A η hr hτ.1.le hτ.2 hεA j k
      rw [abs_le] at hb
      refine ⟨?_, ?_⟩
      · show -(r * _) ≤ r * _
        nlinarith [hb.1, hr.le]
      · show r * _ ≤ r * _
        nlinarith [hb.2, hr.le]
    rw [← Matrix.smul_mulVec]
    exact Mtimes.mtimes_outer _ _ (Set.mem_biUnion hM (Set.mem_image_of_mem _ (hu τ hτ)))
  -- the `r` scaled in above divides back out, leaving the integral itself in the product
  have hrem : (∫ τ in (0:ℝ)..r, (exp (τ • A) - MatExp.expTaylor (τ • A) η) *ᵥ g τ)
      ∈ construct (Mtimes.mtimes (𝕄 := ℐ)
        (MatExp.intervalInputRemainder sys.A r η) U) := by
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
      (MatExp.continuous_expDiff A η).continuousOn
    refine hint _ (D * C) hRmeas fun τ hτ => ?_
    exact le_trans (Matrix.linfty_opNorm_mulVec _ _)
      (mul_le_mul (hD τ ⟨hτ.1.le, hτ.2⟩) (hgbd τ hτ) (norm_nonneg _)
        (le_trans (norm_nonneg _) (hD 0 ⟨le_refl 0, hr.le⟩)))
  -- the same bound per exact order, the factorial and `rⁱ` being constants in `τ`
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
  -- the finite sum of the orders is integrable, which is what lets the integral split
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

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
