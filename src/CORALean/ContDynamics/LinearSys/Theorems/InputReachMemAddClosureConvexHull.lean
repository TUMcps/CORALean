import CORALean.ContDynamics.LinearSys.Operations.InputReach
import CORALean.ContDynamics.LinearSys.Theorems.AestronglyMeasurableReflectIoc
import CORALean.ContDynamics.LinearSys.Theorems.WeightedIntegral
import CORALean.ContDynamics.LinearSys.Theorems.MulVecL
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularCoeff
import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalMulVecSet
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsExpRemainderEntryLe
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ContinuousExpDiff
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpTaylorSmulMulVec
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Convex

/-!
# The exact particular solution, split at order `η`

[1, Prop. 11], eq. (20), encloses `P^U(Δt)` by `⊕_{i≤η} ÃᵢU₀ ⊕ E(Δt,η)ΔtU₀`. The first part holds
exactly: `∫₀^{Δt} e^{Aτ}u(Δt − τ)dτ` splits at order `η`, and every order `i ≤ η` is `Ãᵢ` applied to
a point of `U₀`, the `τⁱ`-weighted mean of the input (`integral_pow_smul_mem`, `U₀` convex and
closed). The tail is the integral of `(e^{Aτ} − Σ_{i≤η}(Aτ)ⁱ/i!)u`, a point of the interval product
`E(Δt,η)ΔtU₀` divided by `Δt` at every `τ` (`abs_expRemainder_entry_le`), so the tail is a point of
that product's closed convex hull. Eq. (20)'s soundness asks for the product itself, which is not
convex; this is what the integral does give.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace MeasureTheory Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

-- a dozen `have`s over `Mat ℝ n n`, each re-solving the local normed-algebra instances
set_option maxHeartbeats 1000000 in
/-- [1, Prop. 11], eq. (20): a point of `P^U(Δt)` is a point of `⊕_{i≤η} ÃᵢU₀` plus a point of the
closed convex hull of `E(Δt,η)ΔtU₀`. -/
theorem LinearSys.inputReach_mem_add_closure_convexHull (sys : LinearSys 𝕋 n) {U : S n}
    (hconv : Convex ℝ (construct U)) (hclosed : IsClosed (construct U))
    (hbdd : Bornology.IsBounded (construct U)) {Δt : ℝ} (hΔt : 0 < Δt) (η : ℕ)
    (hEbdd : Bornology.IsBounded (MatExp.intervalMulVecSet
      (MatExp.expRemainderMat (toRealMat sys.A) Δt η) (Δt • construct U)))
    {y : Vec ℝ n} (hy : y ∈ sys.inputReach U Δt) :
    ∃ x ∈ ∑ i ∈ Finset.Ico 0 (η + 1),
        (fun v => (MatExp.particularCoeff (toRealMat sys.A) Δt i).mulVec v) '' construct U,
      ∃ t ∈ closure (convexHull ℝ (MatExp.intervalMulVecSet
          (MatExp.expRemainderMat (toRealMat sys.A) Δt η) (Δt • construct U))),
        y = x + t := by -- --- PROOF ---
  obtain ⟨u, hmem, hmeas0, rfl⟩ := hy
  set A := toRealMat sys.A with hA
  set E := MatExp.expRemainderMat A Δt η with hE
  set g : ℝ → Vec ℝ n := fun τ => u (Δt - τ) with hg
  have hu : ∀ τ ∈ Set.Ioc (0:ℝ) Δt, g τ ∈ construct U := fun τ hτ =>
    hmem _ ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
  have hmeas : AEStronglyMeasurable g (volume.restrict (Set.Ioc 0 Δt)) :=
    aestronglyMeasurable_reflect_Ioc hmeas0
  obtain ⟨C, hC⟩ := hbdd.exists_norm_le
  -- integrability, from boundedness and measurability, once for every piece
  have hint : ∀ (F : ℝ → Vec ℝ n) (K : ℝ),
      AEStronglyMeasurable F (volume.restrict (Set.Ioc 0 Δt)) →
      (∀ τ ∈ Set.Ioc (0:ℝ) Δt, ‖F τ‖ ≤ K) → IntervalIntegrable F volume 0 Δt := by
    intro F K hFm hFb
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hΔt.le]
    exact ⟨hFm, HasFiniteIntegral.restrict_of_bounded (C := K) measure_Ioc_lt_top
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall hFb))⟩
  have hgbd : ∀ τ ∈ Set.Ioc (0:ℝ) Δt, ‖g τ‖ ≤ C := fun τ hτ => hC _ (hu τ hτ)
  -- the substitution `τ = Δt - s`
  have hsub : (∫ s in (0:ℝ)..Δt, exp ((Δt - s) • A) *ᵥ u s)
      = ∫ τ in (0:ℝ)..Δt, exp (τ • A) *ᵥ g τ := by
    have h := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := Δt)
      (f := fun τ => exp (τ • A) *ᵥ g τ) Δt
    simp only [hg, sub_sub_cancel, sub_self, sub_zero] at h
    exact h
  -- the integrand, split into the exact orders and the remainder
  have hsplit : ∀ τ : ℝ, exp (τ • A) *ᵥ g τ
      = (∑ i ∈ Finset.range (η + 1), ((Nat.factorial i : ℝ)⁻¹ * τ ^ i) • (A ^ i *ᵥ g τ))
        + (exp (τ • A) - MatExp.expTaylor (τ • A) η) *ᵥ g τ := by
    intro τ
    rw [← MatExp.expTaylor_smul_mulVec A η τ (g τ), Matrix.sub_mulVec]
    abel
  -- each exact order is `Ãᵢ` at a point of `U₀`, the `τⁱ`-weighted mean of the input
  have hterm : ∀ i : ℕ, ∃ z ∈ construct U,
      (∫ τ in (0:ℝ)..Δt, ((Nat.factorial i : ℝ)⁻¹ * τ ^ i) • (A ^ i *ᵥ g τ))
        = (MatExp.particularCoeff A Δt i).mulVec z := by
    intro i
    have hgi : IntervalIntegrable (fun τ => τ ^ i • g τ) volume 0 Δt :=
      hint _ (Δt ^ i * C) ((continuous_pow i).aestronglyMeasurable.smul hmeas)
        (fun τ hτ => by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hτ.1.le i)]
          exact mul_le_mul (pow_le_pow_left₀ hτ.1.le hτ.2 i) (hgbd τ hτ) (norm_nonneg _)
            (pow_nonneg hΔt.le i))
    obtain ⟨z, hz, hzeq⟩ := integral_pow_smul_mem hconv hclosed hbdd hΔt i hmeas hu
    refine ⟨z, hz, ?_⟩
    -- the matrix leaves the integral
    have hfun : ∀ τ : ℝ, ((Nat.factorial i : ℝ)⁻¹ * τ ^ i) • (A ^ i *ᵥ g τ)
        = ((Nat.factorial i : ℝ)⁻¹) • ((mulVecL (A ^ i)) (τ ^ i • g τ)) := by
      intro τ
      rw [map_smul, mul_smul]
      rfl
    have hclm : (∫ τ in (0:ℝ)..Δt, (mulVecL (A ^ i)) (τ ^ i • g τ))
        = (mulVecL (A ^ i)) (∫ τ in (0:ℝ)..Δt, τ ^ i • g τ) :=
      ContinuousLinearMap.intervalIntegral_comp_comm _ hgi
    simp only [hfun]
    rw [intervalIntegral.integral_smul, hclm]
    show ((Nat.factorial i : ℝ)⁻¹) • (A ^ i *ᵥ ∫ τ in (0:ℝ)..Δt, τ ^ i • g τ) = _
    rw [← hzeq, Matrix.mulVec_smul, smul_smul, MatExp.particularCoeff, Matrix.smul_mulVec]
    congr 1
    rw [Nat.factorial_succ]
    have h1 : ((i : ℝ) + 1) ≠ 0 := by positivity
    have h2 : (Nat.factorial i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
    push_cast
    field_simp
  -- one weighted mean per order
  choose z hzU hzeq using hterm
  -- the remainder, measured one real entry at a time
  have hgk : ∀ k, AEStronglyMeasurable (fun τ => g τ k) (volume.restrict (Set.Ioc 0 Δt)) := by
    intro k
    rw [aestronglyMeasurable_iff_aemeasurable]
    exact (aemeasurable_pi_iff.mp (aestronglyMeasurable_iff_aemeasurable.mp hmeas)) k
  -- entry by entry, the remainder applied to the input is measurable
  have hRmeas : AEStronglyMeasurable
      (fun τ => (exp (τ • A) - MatExp.expTaylor (τ • A) η) *ᵥ g τ)
      (volume.restrict (Set.Ioc 0 Δt)) := by
    rw [aestronglyMeasurable_iff_aemeasurable]
    refine aemeasurable_pi_iff.mpr fun j => ?_
    have hj : ∀ τ : ℝ, ((exp (τ • A) - MatExp.expTaylor (τ • A) η) *ᵥ g τ) j
        = ∑ k, (exp (τ • A) - MatExp.expTaylor (τ • A) η) j k * g τ k := fun _ => rfl
    simp only [hj]
    rw [← aestronglyMeasurable_iff_aemeasurable]
    have heq : (∑ k : Fin n, (fun τ : ℝ =>
          (exp (τ • A) - MatExp.expTaylor (τ • A) η) j k * g τ k))
        = fun τ : ℝ => ∑ k, (exp (τ • A) - MatExp.expTaylor (τ • A) η) j k * g τ k := by
      funext τ
      simp only [Finset.sum_apply]
    rw [← heq]
    exact Finset.aestronglyMeasurable_sum _ fun k _ =>
      (((MatExp.continuous_expDiff A η).matrix_elem j k).aestronglyMeasurable).mul (hgk k)
  -- at every `τ`, `Δt` times the remainder's value lies in `E(Δt,η)ΔtU₀`
  set Eset := MatExp.intervalMulVecSet E (Δt • construct U) with hEset
  have hpt : ∀ τ ∈ Set.Ioc (0:ℝ) Δt,
      Δt • ((exp (τ • A) - MatExp.expTaylor (τ • A) η) *ᵥ g τ) ∈ Eset := by
    intro τ hτ
    refine ⟨exp (τ • A) - MatExp.expTaylor (τ • A) η, fun j k => ?_, Δt • g τ,
      Set.smul_mem_smul_set (hu τ hτ), Matrix.mulVec_smul _ _ _⟩
    exact (MatExp.abs_expRemainder_entry_le A hτ.1.le hτ.2 η j k).trans (le_abs_self _)
  -- so the remainder's integral lies in the closed convex hull
  set K := closure (convexHull ℝ Eset) with hK
  have hKb : Bornology.IsBounded K := (isBounded_convexHull.mpr hEbdd).closure
  have hrem : (∫ τ in (0:ℝ)..Δt, (exp (τ • A) - MatExp.expTaylor (τ • A) η) *ᵥ g τ) ∈ K := by
    have hI := integral_pow_smul_mem (convex_convexHull ℝ Eset).closure isClosed_closure hKb hΔt 0
      (f := fun τ => Δt • ((exp (τ • A) - MatExp.expTaylor (τ • A) η) *ᵥ g τ))
      (hmeas := hRmeas.fun_const_smul Δt)
      (hmem := fun τ hτ => subset_closure (subset_convexHull ℝ Eset (hpt τ hτ)))
    simp only [pow_zero, one_smul, pow_one, Nat.cast_zero, zero_add, div_one,
      intervalIntegral.integral_smul] at hI
    obtain ⟨w, hw, hweq⟩ := hI
    have hinj : w = ∫ τ in (0:ℝ)..Δt, (exp (τ • A) - MatExp.expTaylor (τ • A) η) *ᵥ g τ :=
      smul_right_injective _ hΔt.ne' hweq
    rwa [← hinj]
  -- everything is integrable, so the split survives the integral
  have hRint : IntervalIntegrable
      (fun τ => (exp (τ • A) - MatExp.expTaylor (τ • A) η) *ᵥ g τ) volume 0 Δt := by
    -- the remainder matrix is continuous, so bounded on `[0, Δt]`
    obtain ⟨D, hD⟩ := (isCompact_Icc (a := (0:ℝ)) (b := Δt)).exists_bound_of_continuousOn
      (MatExp.continuous_expDiff A η).continuousOn
    refine hint _ (D * C) hRmeas fun τ hτ => ?_
    exact le_trans (Matrix.linfty_opNorm_mulVec _ _)
      (mul_le_mul (hD τ ⟨hτ.1.le, hτ.2⟩) (hgbd τ hτ) (norm_nonneg _)
        (le_trans (norm_nonneg _) (hD 0 ⟨le_refl 0, hΔt.le⟩)))
  have hTint : ∀ i ∈ Finset.range (η + 1), IntervalIntegrable
      (fun τ => ((Nat.factorial i : ℝ)⁻¹ * τ ^ i) • (A ^ i *ᵥ g τ)) volume 0 Δt := by
    intro i _
    refine hint _ ((Nat.factorial i : ℝ)⁻¹ * Δt ^ i * (‖A ^ i‖ * C)) ?_ fun τ hτ => ?_
    · exact (continuous_const.mul (continuous_pow i)).aestronglyMeasurable.smul
        ((mulVecL (A ^ i)).continuous.comp_aestronglyMeasurable hmeas)
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (by positivity) (pow_nonneg hτ.1.le i))]
      refine mul_le_mul ?_ (le_trans (Matrix.linfty_opNorm_mulVec _ _)
        (mul_le_mul_of_nonneg_left (hgbd τ hτ) (norm_nonneg _))) (norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hτ.1.le hτ.2 i) (by positivity)
  -- and so is the finite sum of the orders
  have hSint : IntervalIntegrable
      (fun τ => ∑ i ∈ Finset.range (η + 1), ((Nat.factorial i : ℝ)⁻¹ * τ ^ i) • (A ^ i *ᵥ g τ))
      volume 0 Δt := by
    have heq : (∑ i ∈ Finset.range (η + 1),
          (fun τ : ℝ => ((Nat.factorial i : ℝ)⁻¹ * τ ^ i) • (A ^ i *ᵥ g τ)))
        = fun τ : ℝ => ∑ i ∈ Finset.range (η + 1),
            ((Nat.factorial i : ℝ)⁻¹ * τ ^ i) • (A ^ i *ᵥ g τ) := by
      funext τ
      simp only [Finset.sum_apply]
    rw [← heq]
    exact IntervalIntegrable.sum _ hTint
  -- assemble: the orders' sum, and the tail
  refine ⟨∑ i ∈ Finset.Ico 0 (η + 1), (MatExp.particularCoeff A Δt i).mulVec (z i),
    Set.finsetSum_mem_finsetSum _ _ _ fun i _ => ⟨z i, hzU i, rfl⟩, _, hrem, ?_⟩
  rw [hsub]
  simp only [hsplit]
  rw [intervalIntegral.integral_add hSint hRint, intervalIntegral.integral_finsetSum hTint,
    ← Finset.range_eq_Ico]
  simp only [hzeq]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
