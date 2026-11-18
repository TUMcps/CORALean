module

public import CORALean.ContDynamics.LinearSys.Operations.InputReach
public import CORALean.ContDynamics.LinearSys.Theorems.WeightedIntegral
public import CORALean.ContDynamics.LinearSys.Theorems.AestronglyMeasurableReflectIoc
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularCoeff
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsExpRemainderEntryLe
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ContinuousExpDiff
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpTaylorSmulMulVec

@[expose] public section

/-!
# A time-varying input over one step: the Taylor orders of the cube and a box

What an input `u(s) ∈ M [-1, 1]^p` contributes over `[0, r]` is `∫₀ʳ e^{τA} u(r - τ) dτ`. Split
`e^{τA}` into its orders `τⁱAⁱ/i!`, `i ≤ η`, and the remainder `R(τ)`: each order integrates to
`(rⁱ⁺¹/(i+1)!) Aⁱ M bᵢ` with its own `bᵢ ∈ [-1, 1]^p` (`integral_pow_smul_mem` on the convex image
of the cube), and the remainder to a vector within `r Σₖ E(r,η)_lk Σ_c |M_kc|` of zero, the box
`|R(τ)| ≤ E(r,η)` entrywise (`MatExp.abs_expRemainder_entry_le`) puts every `R(τ) u` in. The
orders keep independent factors, as CORA's `aux_overPU` keeps one generator matrix per order;
the remainder is asked of a box, which is convex, rather than of the image of an interval matrix.

## Inputs
* `sys` – linear system
* `M` – generator matrix of the input set
* `r` – step length
* `η` – Taylor order
* `z` – what an input contributes over the step

## Hypotheses
* `hr` – step length positive
* `hz` – `z` is in the input reach of `M [-1, 1]^p` over `r`

## Conclusion
* `z` is a sum of the orders applied to points of the cube plus a vector in the remainder box
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSetLike Scalar NormedSpace MeasureTheory Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n p : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.exists_eq_taylor_add_of_mem_inputReach (sys : LinearSys 𝕋 n) (M : Mat ℝ n p)
    {r : ℝ} (hr : 0 < r) (η : ℕ) {z : Vec ℝ n}
    (hz : z ∈ sys.inputReach (S := ExactSet) ((fun β => M *ᵥ β) '' Set.Icc (-1) 1)
        r) : -- --- CONCL ---
    ∃ b : ℕ → Fin p → ℝ, (∀ i c, |b i c| ≤ 1) ∧ ∃ y : Vec ℝ n,
      (∀ l, |y l| ≤ r * ∑ k, MatExp.expRemainderMat (toRealMat sys.A) r η l k * ∑ c, |M k c|) ∧
      z = (∑ i ∈ Finset.range (η + 1),
        MatExp.particularCoeff (toRealMat sys.A) r i *ᵥ (M *ᵥ b i)) + y := by -- --- PROOF ---
  obtain ⟨u, hmem, hmeas, rfl⟩ := hz
  set A := toRealMat sys.A with hA
  set U : Set (Vec ℝ n) := (fun β => M *ᵥ β) '' Set.Icc (-1) 1 with hU
  set ρ : Vec ℝ n := fun l => ∑ k, MatExp.expRemainderMat A r η l k * ∑ c, |M k c| with hρ
  set g : ℝ → Vec ℝ n := fun τ => u (r - τ) with hg
  -- the input set: the linear image of the cube, convex, closed and bounded
  have hcube : IsCompact (Set.Icc (-1 : Fin p → ℝ) 1) := isCompact_Icc
  have hUc : IsCompact U := hcube.image (Matrix.mulVecLin M).continuous_of_finiteDimensional
  have hUconv : Convex ℝ U := (convex_Icc _ _).linear_image (Matrix.mulVecLin M)
  have hu : ∀ τ ∈ Set.Ioc (0:ℝ) r, g τ ∈ U := fun τ hτ =>
    hmem _ ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
  have hgmeas : AEStronglyMeasurable g (volume.restrict (Set.Ioc 0 r)) := by
    exact aestronglyMeasurable_reflect_Ioc hmeas
  obtain ⟨C, hC⟩ := hUc.isBounded.exists_norm_le
  have hgbd : ∀ τ ∈ Set.Ioc (0:ℝ) r, ‖g τ‖ ≤ C := fun τ hτ => hC _ (hu τ hτ)
  -- integrability, from boundedness and measurability
  have hint : ∀ (F : ℝ → Vec ℝ n) (K : ℝ),
      AEStronglyMeasurable F (volume.restrict (Set.Ioc 0 r)) →
      (∀ τ ∈ Set.Ioc (0:ℝ) r, ‖F τ‖ ≤ K) → IntervalIntegrable F volume 0 r := by
    intro F K hFm hFb
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hr.le]
    exact ⟨hFm, HasFiniteIntegral.restrict_of_bounded (C := K) measure_Ioc_lt_top
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall hFb))⟩
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
  -- each order: `Aⁱ/i!` against `∫ τⁱ g = (rⁱ⁺¹/(i+1)) M bᵢ`
  have hterm : ∀ i, ∃ bi : Fin p → ℝ, (∀ c, |bi c| ≤ 1) ∧
      (∫ τ in (0:ℝ)..r, ((Nat.factorial i : ℝ)⁻¹ * τ ^ i) • (A ^ i *ᵥ g τ))
        = MatExp.particularCoeff A r i *ᵥ (M *ᵥ bi) := by
    -- the weighted input is integrable, and its integral lies in the scaled input set
    intro i
    have hgi : IntervalIntegrable (fun τ => τ ^ i • g τ) volume 0 r :=
      hint _ (r ^ i * C) ((continuous_pow i).aestronglyMeasurable.smul hgmeas)
        (fun τ hτ => by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hτ.1.le i)]
          exact mul_le_mul (pow_le_pow_left₀ hτ.1.le hτ.2 i) (hgbd τ hτ) (norm_nonneg _)
            (pow_nonneg hr.le i))
    have hy : (∫ τ in (0:ℝ)..r, τ ^ i • g τ) ∈ (r ^ (i + 1) / ((i : ℝ) + 1)) • U :=
      integral_pow_smul_mem hUconv hUc.isClosed hUc.isBounded hr i hgmeas hu
    obtain ⟨w, ⟨bi, hbi, rfl⟩, hweq⟩ := hy
    refine ⟨bi, fun c => abs_le.mpr ⟨hbi.1 c, hbi.2 c⟩, ?_⟩
    -- the constant factor and the matrix come out of the integral
    have hpull : (∫ τ in (0:ℝ)..r, ((Nat.factorial i : ℝ)⁻¹ * τ ^ i) • (A ^ i *ᵥ g τ))
        = ((Nat.factorial i : ℝ)⁻¹) • (A ^ i *ᵥ ∫ τ in (0:ℝ)..r, τ ^ i • g τ) := by
      have hfun : ∀ τ : ℝ, ((Nat.factorial i : ℝ)⁻¹ * τ ^ i) • (A ^ i *ᵥ g τ)
          = ((Nat.factorial i : ℝ)⁻¹) • ((Matrix.mulVecLin (A ^ i)) (τ ^ i • g τ)) := by
        intro τ
        rw [map_smul, mul_smul]
        rfl
      have hclm : (∫ τ in (0:ℝ)..r, (Matrix.mulVecLin (A ^ i)).toContinuousLinearMap
            (τ ^ i • g τ))
          = (Matrix.mulVecLin (A ^ i)).toContinuousLinearMap (∫ τ in (0:ℝ)..r, τ ^ i • g τ) :=
        ContinuousLinearMap.intervalIntegral_comp_comm _ hgi
      simp only [hfun]
      rw [intervalIntegral.integral_smul]
      exact congrArg _ hclm
    -- the coefficient: `r^{i+1}/(i+1) / i! = r^{i+1}/(i+1)!`
    rw [hpull, ← hweq, MatExp.particularCoeff, Matrix.mulVec_smul, smul_smul, Matrix.smul_mulVec]
    congr 1
    rw [Nat.factorial_succ]
    have h1 : ((i : ℝ) + 1) ≠ 0 := by positivity
    have h2 : (Nat.factorial i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
    push_cast
    field_simp
  choose b hb hbeq using hterm
  -- the remainder: every `R(τ) g(τ)` is in the box `[-ρ, ρ]`, so its integral in `r` times it
  have hgk : ∀ k, AEStronglyMeasurable (fun τ => g τ k) (volume.restrict (Set.Ioc 0 r)) := by
    intro k
    rw [aestronglyMeasurable_iff_aemeasurable]
    exact (aemeasurable_pi_iff.mp (aestronglyMeasurable_iff_aemeasurable.mp hgmeas)) k
  -- the remainder's integrand is measurable, entry by entry
  have hRmeas : AEStronglyMeasurable
      (fun τ => (exp (τ • A) - MatExp.expTaylor (τ • A) η) *ᵥ g τ)
      (volume.restrict (Set.Ioc 0 r)) := by
    rw [aestronglyMeasurable_iff_aemeasurable]
    refine aemeasurable_pi_iff.mpr fun j => ?_
    have hj : ∀ τ : ℝ, ((exp (τ • A) - MatExp.expTaylor (τ • A) η) *ᵥ g τ) j
        = ∑ k, (exp (τ • A) - MatExp.expTaylor (τ • A) η) j k * g τ k := fun _ => rfl
    simp only [hj]
    rw [← aestronglyMeasurable_iff_aemeasurable]
    -- a sum of measurable products, as a function
    have heq : (∑ k : Fin n, (fun τ : ℝ =>
          (exp (τ • A) - MatExp.expTaylor (τ • A) η) j k * g τ k))
        = fun τ : ℝ => ∑ k, (exp (τ • A) - MatExp.expTaylor (τ • A) η) j k * g τ k := by
      funext τ
      simp only [Finset.sum_apply]
    rw [← heq]
    exact Finset.aestronglyMeasurable_sum _ fun k _ =>
      (((MatExp.continuous_expDiff A η).matrix_elem j k).aestronglyMeasurable).mul (hgk k)
  have hbox : ∀ τ ∈ Set.Ioc (0:ℝ) r,
      (exp (τ • A) - MatExp.expTaylor (τ • A) η) *ᵥ g τ ∈ Set.Icc (-ρ) ρ := by
    intro τ hτ
    obtain ⟨β, hβ, hβeq⟩ := hu τ hτ
    -- `|g_k| ≤ Σ_c |M_kc|` and `|R_lk| ≤ E_lk`
    have hgk : ∀ k, |g τ k| ≤ ∑ c, |M k c| := by
      intro k
      rw [← hβeq]
      show |∑ c, M k c * β c| ≤ _
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun c _ => ?_)
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (abs_le.mpr ⟨hβ.1 c, hβ.2 c⟩)
    -- each entry of the remainder's integrand within `ρ`
    have hl : ∀ l, |((exp (τ • A) - MatExp.expTaylor (τ • A) η) *ᵥ g τ) l| ≤ ρ l := by
      intro l
      show |∑ k, (exp (τ • A) - MatExp.expTaylor (τ • A) η) l k * g τ k| ≤ _
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun k _ => ?_)
      rw [abs_mul]
      exact mul_le_mul (MatExp.abs_expRemainder_entry_le A hτ.1.le hτ.2 η l k) (hgk k)
        (abs_nonneg _) (le_trans (abs_nonneg _) (MatExp.abs_expRemainder_entry_le A hτ.1.le
          hτ.2 η l k))
    exact ⟨fun l => by have := hl l; rw [abs_le] at this; simp only [Pi.neg_apply]; linarith,
      fun l => by have := hl l; rw [abs_le] at this; linarith⟩
  have hrem : (∫ τ in (0:ℝ)..r, (exp (τ • A) - MatExp.expTaylor (τ • A) η) *ᵥ g τ)
      ∈ r • Set.Icc (-ρ) ρ := by
    have hI := integral_pow_smul_mem (convex_Icc _ _) isClosed_Icc (Metric.isBounded_Icc _ _) hr 0
      hRmeas hbox
    simpa using hI
  obtain ⟨y', hy', hy'eq⟩ := hrem
  -- everything is integrable, so the split survives the integral
  have hRint : IntervalIntegrable
      (fun τ => (exp (τ • A) - MatExp.expTaylor (τ • A) η) *ᵥ g τ) volume 0 r := by
    obtain ⟨D, hD⟩ := (isCompact_Icc (a := (0:ℝ)) (b := r)).exists_bound_of_continuousOn
      (MatExp.continuous_expDiff A η).continuousOn
    refine hint _ (D * C) hRmeas fun τ hτ => ?_
    exact le_trans (Matrix.linfty_opNorm_mulVec _ _)
      (mul_le_mul (hD τ ⟨hτ.1.le, hτ.2⟩) (hgbd τ hτ) (norm_nonneg _)
        (le_trans (norm_nonneg _) (hD 0 ⟨le_refl 0, hr.le⟩)))
  -- each Taylor term is integrable, bounded by its coefficient
  have hTint : ∀ i ∈ Finset.range (η + 1), IntervalIntegrable
      (fun τ => ((Nat.factorial i : ℝ)⁻¹ * τ ^ i) • (A ^ i *ᵥ g τ)) volume 0 r := by
    intro i _
    refine hint _ ((Nat.factorial i : ℝ)⁻¹ * r ^ i * (‖A ^ i‖ * C)) ?_ fun τ hτ => ?_
    · exact (continuous_const.mul (continuous_pow i)).aestronglyMeasurable.smul
        ((Matrix.mulVecLin (A ^ i)).continuous_of_finiteDimensional.comp_aestronglyMeasurable
          hgmeas)
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (by positivity) (pow_nonneg hτ.1.le i))]
      refine mul_le_mul ?_ (le_trans (Matrix.linfty_opNorm_mulVec _ _)
        (mul_le_mul_of_nonneg_left (hgbd τ hτ) (norm_nonneg _))) (norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hτ.1.le hτ.2 i) (by positivity)
  -- and so is their sum
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
  refine ⟨b, hb, r • y', fun l => ?_, ?_⟩
  · -- the box scaled by `r`
    have h1 := hy'.1 l
    have h2 := hy'.2 l
    simp only [Pi.neg_apply] at h1
    show |r * y' l| ≤ r * ρ l
    rw [abs_mul, abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨h1, h2⟩) hr.le
  · rw [hsub]
    simp only [hsplit]
    rw [intervalIntegral.integral_add hSint hRint, intervalIntegral.integral_finsetSum hTint,
      ← hy'eq]
    congr 1
    exact Finset.sum_congr rfl fun i _ => hbeq i

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
