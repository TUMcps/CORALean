module

public import CORALean.ContDynamics.LinParamSys.Operations.InputSolutionZono
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ContinuousExpDiff
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpTaylorSmulMulVec
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalInputRemainder
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.RemainderEntryLe
public import CORALean.ContDynamics.LinearSys.Theorems.MulVecL
public import CORALean.ContDynamics.LinearSys.Theorems.WeightedIntegral
public import CORALean.ContSet.Interval.Real.Theorems.MatPowOuter
public import CORALean.ContSet.Interval.Real.Theorems.MemMat
public import CORALean.ContSet.Interval.Real.Theorems.NormLeAbsMax
public import CORALean.ContSet.Interval.Real.Theorems.SmulOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.MapExact
public import CORALean.ContSet.Zonotope.Real.Theorems.MatPowOuter
public import Mathlib.Algebra.Order.Ring.Star

@[expose] public section

/-!
# `inputSolutionZono` contains what the input contributes at every matrix of the set

[1, Prop. 3.6] at a matrix drawn from `construct sys.A`, the run being
`'constParam'` as in `InputSolutionOuter`. The Taylor sum splits into four
pieces rather than two: orders `0` and `1` land in `inputTermZono` by
`matPow_outer` at the matrix zonotope, orders `2` through `η` and the remainder
land in the interval-matrix pieces by the same argument `InputSolutionOuter`
already makes, now at `sys.A.interval` rather than a set-valued matrix given
directly.

`2 ≤ η` is what makes the split legitimate: below it the printed formula's
"order `1`, then orders `2 … η`" reading does not correspond to any truncation
of the exponential, `expTaylor _ 0` not reaching order `1` at all.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
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
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes 𝕄𝒵 S] [Mtimes ℐ S]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [Mtimes 𝕄𝒵 S] in
/-- The tail, by induction on the order past two: `plus` absorbs one term at a
time, exactly as `inputTaylorSumTail` builds it. -/
theorem LinParamSys.aux_inputTaylorSumTail_outer (sys : LinParamSys ℐ n) (r : ℝ) (U : S n)
    (x : ℕ → Vec ℝ n) : ∀ (m : ℕ),
    (∀ i, 2 ≤ i → i ≤ m + 2 →
      x i ∈ construct (Mtimes.mtimes (𝕄 := ℐ) (sys.inputTerm r i) U)) →
    (∑ i ∈ Finset.Ico 2 (m + 3), x i) ∈ construct (sys.inputTaylorSumTail r U (m + 2))
  | 0, hx => by
      rw [Nat.Ico_succ_singleton, Finset.sum_singleton]
      exact hx 2 (le_refl 2) (le_refl 2)
  | k + 1, hx => by
      rw [Finset.sum_Ico_succ_top (by omega : 2 ≤ k + 1 + 2)]
      exact Plus.plus_outer _ _ (Set.add_mem_add
        (sys.aux_inputTaylorSumTail_outer r U x k fun i hi2 hik => hx i hi2 (by omega))
        (hx (k + 1 + 2) (by omega) (le_refl _)))


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinParamSys.inputSolutionZono_outer (sys : LinParamSys 𝕄𝒵 n)
    {r : ℝ} (hr : 0 < r) {η : ℕ} (hη : 2 ≤ η)
    (hε : ‖(Interval.smul r sys.A.interval).absMax‖ / ((η : ℝ) + 2) < 1)
    {A : Mat ℝ n n} (hA : A ∈ construct sys.A) {U : S n}
    (hconv : Convex ℝ (construct U)) (hclosed : IsClosed (construct U))
    (hbdd : Bornology.IsBounded (construct U))
    -- the next three are asked of the product and not of `U`, `R(τ)` varying with `τ`
    (hRconv : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.intervalInputRemainder sys.A.interval r η) U)))
    (hRclosed : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.intervalInputRemainder sys.A.interval r η) U)))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.intervalInputRemainder sys.A.interval r η) U)))
    {u : ℝ → Vec ℝ n}
    (hu : ∀ τ ∈ Set.Ioc (0:ℝ) r, u (r - τ) ∈ construct U)
    (hmeas : AEStronglyMeasurable (fun τ => u (r - τ)) (volume.restrict (Set.Ioc 0 r))) :
    (∫ s in (0:ℝ)..r, exp ((r - s) • A) *ᵥ u s)
      ∈ construct (sys.inputSolutionZono r η U) := by -- --- PROOF ---
  obtain ⟨m, hm⟩ := Nat.le.dest hη
  have hηeq : η = m + 2 := by omega
  subst hηeq
  -- the condition is checkable from the box; the member's own is what the tail needs
  have hA' : A ∈ construct sys.A.interval := Zonotope.interval_contains sys.A hA
  have hnorm : ‖r • A‖ ≤ ‖(Interval.smul r sys.A.interval).absMax‖ :=
    Interval.norm_le_absMax (Interval.smul_outer r sys.A.interval hA')
  have hεA : ‖r • A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1 := lt_of_le_of_lt (by gcongr) hε
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
  -- one order's contribution to the integrand, common to both families
  set f : ℕ → ℝ → Vec ℝ n :=
    fun i τ => ((Nat.factorial i : ℝ)⁻¹ * τ ^ i) • (A ^ i *ᵥ g τ) with hf
  -- the raw finite sum, exactly as `expTaylor` unfolds it
  have hsplit0 : ∀ τ : ℝ, exp (τ • A) *ᵥ g τ
      = (∑ i ∈ Finset.range (m + 2 + 1), f i τ)
        + (exp (τ • A) - MatExp.expTaylor (τ • A) (m + 2)) *ᵥ g τ := by
    intro τ
    simp only [hf]
    rw [← MatExp.expTaylor_smul_mulVec A (m + 2) τ (g τ), Matrix.sub_mulVec]
    abel
  -- the same sum, split at order two
  have hrangeSplit : ∀ τ : ℝ, (∑ i ∈ Finset.range (m + 2 + 1), f i τ)
      = (f 0 τ + f 1 τ) + ∑ i ∈ Finset.Ico 2 (m + 2 + 1), f i τ := by
    intro τ
    rw [← Finset.sum_range_add_sum_Ico (fun i => f i τ) (show 2 ≤ m + 2 + 1 by omega),
      Finset.sum_range_succ, Finset.sum_range_one]
  have hsplit : ∀ τ : ℝ, exp (τ • A) *ᵥ g τ
      = ((f 0 τ + f 1 τ) + ∑ i ∈ Finset.Ico 2 (m + 2 + 1), f i τ)
        + (exp (τ • A) - MatExp.expTaylor (τ • A) (m + 2)) *ᵥ g τ := by
    intro τ
    rw [hsplit0 τ, hrangeSplit τ]
  -- integrability of one order, common to both families and every order
  have hTint : ∀ i : ℕ, IntervalIntegrable (f i) volume 0 r := by
    intro i
    refine hint _ ((Nat.factorial i : ℝ)⁻¹ * r ^ i * (‖A ^ i‖ * C)) ?_ fun τ hτ => ?_
    · exact (continuous_const.mul (continuous_pow i)).aestronglyMeasurable.smul
        ((mulVecL (A ^ i)).continuous.comp_aestronglyMeasurable hmeas)
    · show ‖((Nat.factorial i : ℝ)⁻¹ * τ ^ i) • (A ^ i *ᵥ g τ)‖ ≤ _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (by positivity) (pow_nonneg hτ.1.le i))]
      refine mul_le_mul ?_ (le_trans (Matrix.linfty_opNorm_mulVec _ _)
        (mul_le_mul_of_nonneg_left (hgbd τ hτ) (norm_nonneg _))) (norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hτ.1.le hτ.2 i) (by positivity)
  -- order `i`'s integral, with the matrix pulled out of it: common to both families
  have hpull : ∀ i : ℕ, (∫ τ in (0:ℝ)..r, f i τ)
      = ((Nat.factorial i : ℝ)⁻¹) • (A ^ i *ᵥ ∫ τ in (0:ℝ)..r, τ ^ i • g τ) := by
    intro i
    have hgi : IntervalIntegrable (fun τ => τ ^ i • g τ) volume 0 r :=
      hint _ (r ^ i * C) ((continuous_pow i).aestronglyMeasurable.smul hmeas)
        (fun τ hτ => by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hτ.1.le i)]
          exact mul_le_mul (pow_le_pow_left₀ hτ.1.le hτ.2 i) (hgbd τ hτ) (norm_nonneg _)
            (pow_nonneg hr.le i))
    have hfun : ∀ τ : ℝ, f i τ
        = ((Nat.factorial i : ℝ)⁻¹) • ((mulVecL (A ^ i)) (τ ^ i • g τ)) := by
      intro τ
      show ((Nat.factorial i : ℝ)⁻¹ * τ ^ i) • (A ^ i *ᵥ g τ) = _
      rw [map_smul, mul_smul]; rfl
    simp only [hfun]
    rw [intervalIntegral.integral_smul,
      ContinuousLinearMap.intervalIntegral_comp_comm _ hgi]
    rfl
  -- the weighted average of `U` at order `i`, that both families pull `z` from
  have hy : ∀ i : ℕ, (∫ τ in (0:ℝ)..r, τ ^ i • g τ)
      ∈ (r ^ (i + 1) / ((i : ℝ) + 1)) • construct U :=
    fun i => integral_pow_smul_mem hconv hclosed hbdd hr i hmeas hu
  -- `Aⁱ/i!` against `r^(i+1)/(i+1)` is exactly the matrix `inputTerm`/`inputTermZono` name
  have hcomb : ∀ (i : ℕ) (z : Vec ℝ n),
      ((Nat.factorial i : ℝ)⁻¹) • (A ^ i *ᵥ ((r ^ (i + 1) / ((i : ℝ) + 1)) • z))
        = ((r ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)) • A ^ i) *ᵥ z := by
    intro i z
    rw [Matrix.mulVec_smul, smul_smul, Matrix.smul_mulVec]
    congr 1
    rw [Nat.factorial_succ]
    have h1 : ((i : ℝ) + 1) ≠ 0 := by positivity
    have h2 : (Nat.factorial i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
    push_cast; field_simp
  -- orders `0` and `1`: exact, through the matrix zonotope
  have htermZ : ∀ i : ℕ, (∫ τ in (0:ℝ)..r, f i τ)
      ∈ construct (Mtimes.mtimes (𝕄 := 𝕄𝒵) (sys.inputTermZono r i) U) := by
    intro i
    obtain ⟨z, hz, hzeq⟩ := hy i
    rw [hpull i, ← hzeq, hcomb i z]
    have hAmem : ((r ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)) • A ^ i)
        ∈ construct (sys.inputTermZono r i) := by
      show _ ∈ (sys.inputTermZono r i).construct
      rw [LinParamSys.inputTermZono, ← Zonotope.map_exact]
      exact ⟨A ^ i, Zonotope.matPow_outer sys.A hA i, rfl⟩
    exact Mtimes.mtimes_outer _ _ (Set.mem_biUnion hAmem (Set.mem_image_of_mem _ hz))
  -- orders `2` through `m + 2`: over-approximated, through the enclosing interval matrix
  have htermI : ∀ i : ℕ, (∫ τ in (0:ℝ)..r, f i τ)
      ∈ construct (Mtimes.mtimes (𝕄 := ℐ)
        ((LinParamSys.mk (𝕄 := ℐ) sys.A.interval).inputTerm r i) U) := by
    intro i
    obtain ⟨z, hz, hzeq⟩ := hy i
    rw [hpull i, ← hzeq, hcomb i z]
    exact Mtimes.mtimes_outer _ _ (Set.mem_biUnion
      (Interval.smul_outer _ _ (Interval.matPow_outer sys.A.interval hA' i))
      (Set.mem_image_of_mem _ hz))
  -- `Matrix` blocks instance search, so the remainder is measured one real entry at a time
  have hgk : ∀ k, AEStronglyMeasurable (fun τ => g τ k) (volume.restrict (Set.Ioc 0 r)) := by
    intro k
    rw [aestronglyMeasurable_iff_aemeasurable]
    exact (aemeasurable_pi_iff.mp (aestronglyMeasurable_iff_aemeasurable.mp hmeas)) k
  have hRmeas : AEStronglyMeasurable
      (fun τ => (exp (τ • A) - MatExp.expTaylor (τ • A) (m + 2)) *ᵥ g τ)
      (volume.restrict (Set.Ioc 0 r)) := by
    rw [aestronglyMeasurable_iff_aemeasurable]
    refine aemeasurable_pi_iff.mpr fun j => ?_
    have hj : ∀ τ : ℝ, ((exp (τ • A) - MatExp.expTaylor (τ • A) (m + 2)) *ᵥ g τ) j
        = ∑ k, (exp (τ • A) - MatExp.expTaylor (τ • A) (m + 2)) j k * g τ k := fun _ => rfl
    simp only [hj]
    rw [← aestronglyMeasurable_iff_aemeasurable]
    -- `Finset.aestronglyMeasurable_sum` sums functions, the goal sums values
    have heq : (∑ k : Fin n, (fun τ : ℝ =>
          (exp (τ • A) - MatExp.expTaylor (τ • A) (m + 2)) j k * g τ k))
        = fun τ : ℝ =>
          ∑ k, (exp (τ • A) - MatExp.expTaylor (τ • A) (m + 2)) j k * g τ k := by
      funext τ; simp only [Finset.sum_apply]
    rw [← heq]
    exact Finset.aestronglyMeasurable_sum _ fun k _ =>
      (((MatExp.continuous_expDiff A (m + 2)).matrix_elem j k).aestronglyMeasurable).mul (hgk k)
  -- every entry of `r · R(τ)` lies in the member's remainder, and so in the box's
  have hpt : ∀ τ ∈ Set.Ioc (0:ℝ) r,
      r • ((exp (τ • A) - MatExp.expTaylor (τ • A) (m + 2)) *ᵥ g τ)
        ∈ construct (Mtimes.mtimes (𝕄 := ℐ)
        (MatExp.intervalInputRemainder sys.A.interval r (m + 2)) U) := by
    intro τ hτ
    have hM : (r • (exp (τ • A) - MatExp.expTaylor (τ • A) (m + 2)))
        ∈ (MatExp.intervalInputRemainder sys.A.interval r (m + 2)).construct := by
      refine MatExp.intervalInputRemainder_contains sys.A.interval hr (m + 2) hε hA' ?_
      refine Interval.mem_mat_iff.mpr fun j k => ?_
      have hb := MatExp.remainder_entry_le A (m + 2) hr hτ.1.le hτ.2 hεA j k
      rw [abs_le] at hb
      refine ⟨?_, ?_⟩
      · show -(r * _) ≤ r * _
        nlinarith [hb.1, hr.le]
      · show r * _ ≤ r * _
        nlinarith [hb.2, hr.le]
    rw [← Matrix.smul_mulVec]
    exact Mtimes.mtimes_outer _ _ (Set.mem_biUnion hM (Set.mem_image_of_mem _ (hu τ hτ)))
  -- the `r` scaled in above divides back out, leaving the integral itself in the product
  have hrem :
      (∫ τ in (0:ℝ)..r, (exp (τ • A) - MatExp.expTaylor (τ • A) (m + 2)) *ᵥ g τ)
      ∈ construct (Mtimes.mtimes (𝕄 := ℐ)
        (MatExp.intervalInputRemainder sys.A.interval r (m + 2)) U) := by
    have hI := integral_pow_smul_mem hRconv hRclosed hRbdd hr 0
      (f := fun τ => r • ((exp (τ • A) - MatExp.expTaylor (τ • A) (m + 2)) *ᵥ g τ))
      (hmeas := hRmeas.fun_const_smul r) (hmem := hpt)
    simp only [pow_zero, one_smul, pow_one, Nat.cast_zero, zero_add, div_one,
      intervalIntegral.integral_smul] at hI
    obtain ⟨y, hy', hyeq⟩ := hI
    have hinj : y
        = ∫ τ in (0:ℝ)..r, (exp (τ • A) - MatExp.expTaylor (τ • A) (m + 2)) *ᵥ g τ :=
      smul_right_injective _ hr.ne' hyeq
    rwa [← hinj]
  -- everything is integrable, so the split survives the integral
  have hRint : IntervalIntegrable
      (fun τ => (exp (τ • A) - MatExp.expTaylor (τ • A) (m + 2)) *ᵥ g τ) volume 0 r := by
    obtain ⟨D, hD⟩ := (isCompact_Icc (a := (0:ℝ)) (b := r)).exists_bound_of_continuousOn
      (MatExp.continuous_expDiff A (m + 2)).continuousOn
    refine hint _ (D * C) hRmeas fun τ hτ => ?_
    exact le_trans (Matrix.linfty_opNorm_mulVec _ _)
      (mul_le_mul (hD τ ⟨hτ.1.le, hτ.2⟩) (hgbd τ hτ) (norm_nonneg _)
        (le_trans (norm_nonneg _) (hD 0 ⟨le_refl 0, hr.le⟩)))
  -- every piece of the split is integrable, so the split survives the integral
  have hS01int : IntervalIntegrable (fun τ => f 0 τ + f 1 τ) volume 0 r :=
    (hTint 0).add (hTint 1)
  have hTailIntEach : ∀ i ∈ Finset.Ico 2 (m + 2 + 1), IntervalIntegrable (f i) volume 0 r :=
    fun i _ => hTint i
  have hTailInt : IntervalIntegrable (fun τ => ∑ i ∈ Finset.Ico 2 (m + 2 + 1), f i τ)
      volume 0 r := by
    have heq : (∑ i ∈ Finset.Ico 2 (m + 2 + 1), (fun τ : ℝ => f i τ))
        = fun τ : ℝ => ∑ i ∈ Finset.Ico 2 (m + 2 + 1), f i τ := by
      funext τ; simp only [Finset.sum_apply]
    rw [← heq]
    exact IntervalIntegrable.sum _ hTailIntEach
  have hHeadTailInt : IntervalIntegrable
      (fun τ => (f 0 τ + f 1 τ) + ∑ i ∈ Finset.Ico 2 (m + 2 + 1), f i τ) volume 0 r :=
    hS01int.add hTailInt
  -- the split survives the integral, one addition and one finite sum at a time
  rw [hsub]
  simp only [hsplit]
  rw [intervalIntegral.integral_add hHeadTailInt hRint,
    intervalIntegral.integral_add hS01int hTailInt,
    intervalIntegral.integral_add (hTint 0) (hTint 1),
    intervalIntegral.integral_finsetSum hTailIntEach]
  exact Plus.plus_outer _ _ (Set.add_mem_add
    (Plus.plus_outer _ _ (Set.add_mem_add
      (Plus.plus_outer _ _ (Set.add_mem_add (htermZ 0) (htermZ 1)))
      ((LinParamSys.mk (𝕄 := ℐ) sys.A.interval).aux_inputTaylorSumTail_outer r U _ m
        fun i _ _ => htermI i)))
    hrem)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
