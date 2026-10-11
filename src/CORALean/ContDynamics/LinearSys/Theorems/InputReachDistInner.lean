import CORALean.ContDynamics.LinearSys.Operations.InputSolutionInner
import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralConstInput
import CORALean.ContDynamics.LinearSys.Theorems.IntervalIntegrableExpSubMulVec
import CORALean.ContDynamics.LinearSys.Theorems.IntervalIntegrableOfMemBounded
import CORALean.ContDynamics.LinearSys.Theorems.WeightedIntegral
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormExpSmulSubOneLe

/-!
# A step of the exact particular solution is within `O(Δt²)` of a constant input

The estimate [1, Prop. 1] rests on, and the reason its error is second order in
the step rather than first: replacing an input by the *mean* `Δt⁻¹∫₀^{Δt}u`,
which `integral_pow_smul_mem` puts back in `U`, cancels the whole zeroth order,
`∫₀^{Δt}(u(σ) - s)dσ = 0`, and leaves `∫₀^{Δt}(e^{A(Δt-σ)} - I)(u(σ) - s)dσ`.
Both factors there are `O(Δt)` and `O(1)`, so the integral is `O(Δt²)`.

Convexity and closedness of `U` are what the mean needs; any other point of `U`
would only give `O(Δt)`, which summed over `t/Δt` steps converges to nothing.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed
      Continuous-Time Linear Systems Using Set Propagation". arXiv:2310.19083,
      2023.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
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

/-- Every point of the exact one-step particular solution is `O(Δt²)` from the
inner approximation. -/
theorem LinearSys.inputReach_dist_inputSolutionInner (sys : LinearSys 𝕋 n) {U : S n}
    {Δt ρ : ℝ} (hΔt : 0 < Δt) (hconv : Convex ℝ (construct U))
    (hclosed : IsClosed (construct U)) (hbdd : Bornology.IsBounded (construct U))
    (hρ : ∀ v ∈ construct U, ‖v‖ ≤ ρ) :
    ∀ x ∈ sys.inputReach U Δt, ∃ y ∈ sys.inputSolutionInner U Δt,
      ‖x - y‖ ≤ 2 * ρ * ‖toRealMat sys.A‖ * Real.exp (Δt * ‖toRealMat sys.A‖)
        * Δt ^ 2 := by -- --- PROOF ---
  set A := toRealMat sys.A with hA
  rintro x ⟨u, hu, hmeas, rfl⟩
  have hmeasIoc : AEStronglyMeasurable u (volume.restrict (Set.Ioc 0 Δt)) :=
    hmeas.mono_measure (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl)
  -- the mean input over the step, which convexity and closedness put back in `U`
  have hmean : (∫ τ in (0:ℝ)..Δt, u τ) ∈ Δt • construct U := by
    have h := integral_pow_smul_mem hconv hclosed hbdd hΔt 0 hmeasIoc
      (fun τ hτ => hu τ ⟨hτ.1.le, hτ.2⟩)
    simpa using h
  obtain ⟨s, hs, hseq⟩ := hmean
  have hρ0 : 0 ≤ ρ := le_trans (norm_nonneg _) (hρ _ (hu 0 ⟨le_refl 0, hΔt.le⟩))
  refine ⟨MatExp.expIntegral A Δt *ᵥ s, ⟨s, hs, rfl⟩, ?_⟩
  -- the inner point as the same integral at the constant input
  have hy : MatExp.expIntegral A Δt *ᵥ s = ∫ σ in (0:ℝ)..Δt, exp ((Δt - σ) • A) *ᵥ s :=
    (Real.MatExp.expIntegral_constInput A s hΔt.le).symm
  have hf1 : IntervalIntegrable (fun σ => exp ((Δt - σ) • A) *ᵥ u σ) volume 0 Δt :=
    intervalIntegrable_expSub_mulVec (A := A) (U := U) hΔt.le hbdd hu hmeas
  have hf2 : IntervalIntegrable (fun σ => exp ((Δt - σ) • A) *ᵥ s) volume 0 Δt :=
    intervalIntegrable_expSub_mulVec (A := A) (U := U) hΔt.le hbdd (fun _ _ => hs)
      aestronglyMeasurable_const
  have huint : IntervalIntegrable u volume 0 Δt :=
    intervalIntegrable_of_mem_bounded (U := U) hΔt.le hbdd hu hmeas
  have hh : IntervalIntegrable (fun σ => u σ - s) volume 0 Δt :=
    huint.sub intervalIntegrable_const
  -- the zeroth order cancels, by the choice of `s`
  have hhz : (∫ σ in (0:ℝ)..Δt, (u σ - s)) = 0 := by
    rw [intervalIntegral.integral_sub huint intervalIntegrable_const,
      intervalIntegral.integral_const, ← hseq]
    simp
  have hgh : IntervalIntegrable
      (fun σ => (exp ((Δt - σ) • A) - (1 : Mat ℝ n n)) *ᵥ (u σ - s)) volume 0 Δt := by
    have heq : (fun σ => (exp ((Δt - σ) • A) - (1 : Mat ℝ n n)) *ᵥ (u σ - s))
        = fun σ => (exp ((Δt - σ) • A) *ᵥ u σ - exp ((Δt - σ) • A) *ᵥ s) - (u σ - s) := by
      funext σ
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub]
    rw [heq]
    exact (hf1.sub hf2).sub hh
  -- what is left of the difference once the zeroth order is gone
  have hxy : (∫ σ in (0:ℝ)..Δt, exp ((Δt - σ) • A) *ᵥ u σ) - MatExp.expIntegral A Δt *ᵥ s
      = ∫ σ in (0:ℝ)..Δt, (exp ((Δt - σ) • A) - (1 : Mat ℝ n n)) *ᵥ (u σ - s) := by
    have hsplit : ∀ σ : ℝ, exp ((Δt - σ) • A) *ᵥ u σ - exp ((Δt - σ) • A) *ᵥ s
        = (exp ((Δt - σ) • A) - (1 : Mat ℝ n n)) *ᵥ (u σ - s) + (u σ - s) := by
      intro σ
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub]
      abel
    rw [hy, ← intervalIntegral.integral_sub hf1 hf2]
    simp only [hsplit]
    rw [intervalIntegral.integral_add hgh hh, hhz, add_zero]
  rw [hxy]
  -- both factors bounded on the window, the first by `Δt‖A‖e^{Δt‖A‖}`
  have hbound : ∀ σ ∈ Set.uIoc (0:ℝ) Δt, ‖(exp ((Δt - σ) • A) - (1 : Mat ℝ n n)) *ᵥ (u σ - s)‖
      ≤ (Δt * ‖A‖ * Real.exp (Δt * ‖A‖)) * (2 * ρ) := by
    intro σ hσ
    rw [Set.uIoc_of_le hΔt.le] at hσ
    have hle : (0:ℝ) ≤ Δt - σ := by linarith [hσ.2]
    have hmono : (Δt - σ) * ‖A‖ ≤ Δt * ‖A‖ :=
      mul_le_mul_of_nonneg_right (by linarith [hσ.1]) (norm_nonneg _)
    have hexp : (Δt - σ) * ‖A‖ * Real.exp ((Δt - σ) * ‖A‖) ≤ Δt * ‖A‖ * Real.exp (Δt * ‖A‖) :=
      mul_le_mul hmono (Real.exp_le_exp.mpr hmono) (Real.exp_nonneg _)
        (mul_nonneg hΔt.le (norm_nonneg _))
    have h1 : ‖exp ((Δt - σ) • A) - 1‖ ≤ Δt * ‖A‖ * Real.exp (Δt * ‖A‖) :=
      le_trans (norm_exp_smul_sub_one_le A hle) hexp
    -- and the second by twice the radius of `U`, both points lying in it
    have h2 : ‖u σ - s‖ ≤ 2 * ρ := by
      refine le_trans (norm_sub_le _ _) ?_
      have := hρ _ (hu σ ⟨hσ.1.le, hσ.2⟩)
      have := hρ _ hs
      linarith
    exact le_trans (Matrix.linfty_opNorm_mulVec _ _)
      (mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg (mul_nonneg hΔt.le (norm_nonneg _))
        (Real.exp_nonneg _)))
  refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const hbound) ?_
  rw [sub_zero, abs_of_pos hΔt]
  ring_nf
  exact le_refl _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
