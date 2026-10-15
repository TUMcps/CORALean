module

public import CORALean.ContDynamics.LinearSys.Theorems.FlowIci
public import CORALean.ContDynamics.LinearSys.Theorems.HasDerivWithinAtExpNegMulVec
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-!
# What a classical run's `variation_of_constants` assumes about the input

`IsCanonicalClassicalTrajectory` puts no regularity on `u`, and none has to be added: the flow pins
`u` to the derivative of `x`, so the integrand `e^{-As} u(s)` is itself a
derivative — of `e^{-As} x(s)`. A derivative within `Ici s` is measurable in `s`
for *any* function, so measurability costs nothing.

Boundedness is the one thing that comes from outside, and from the input set
rather than from `u`: a bounded `U` bounds the integrand together with the
exponential, which is continuous over a compact step.

The statement asks only that the domain cover the window `[a, b]` it speaks about,
so the identity pinning `u` holds on the half-open window alone — enough, the
missing point being null. Kept for a classical run on a window `[kΔt, (k+1)Δt]`
that does not reach back to `0` — a nonlinear run linearized step by step — where
`IsCanonicalClassicalTrajectory.trajectory` cannot hand it to `IsTrajectory`, whose integral
equation is anchored at `0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-August-2026
-- Last update:   10-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The integrand is the derivative of the substituted trajectory, taken within
`Ici s`: the form Mathlib's measurability lemma speaks about, and no weaker, the
two agreeing wherever the domain still extends to the right of `s`. -/
theorem LinearSys.IsCanonicalClassicalTrajectory.aux_integrand_eq_derivWithin {sys : LinearSys 𝕋 n}
    {T : Set ℝ}
    {R₀ U : S n} {x u : ℝ → Vec ℝ n} (traj : sys.IsCanonicalClassicalTrajectory T R₀ U x u)
        {a b s : ℝ}
    (hT : Set.Icc a b ⊆ T) (hs : s ∈ Set.Ico a b) :
    exp ((-s) • toRealMat sys.A) *ᵥ u s
      = derivWithin (fun r : ℝ => exp ((-r) • toRealMat sys.A) *ᵥ x r) (Set.Ici s) s :=
  ((hasDerivWithinAt_expNeg_mulVec (toRealMat sys.A) x u (Set.Ici s) s
    (traj.flow_Ici hT hs)).derivWithin (uniqueDiffWithinAt_Ici s)).symm

/-- Measurable with nothing assumed of `u`: `stronglyMeasurable_derivWithin_Ici`
holds for every function, and the integrand is a derivative of that shape almost
everywhere on the window. -/
theorem LinearSys.IsCanonicalClassicalTrajectory.aux_aestronglyMeasurable {sys : LinearSys 𝕋 n}
    {T : Set ℝ}
    {R₀ U : S n} {x u : ℝ → Vec ℝ n} {a b : ℝ}
    (traj : sys.IsCanonicalClassicalTrajectory T R₀ U x u)
    (hT : Set.Icc a b ⊆ T) :
    AEStronglyMeasurable (fun s => exp ((-s) • toRealMat sys.A) *ᵥ u s)
      (volume.restrict (Set.Ioc a b)) := by -- --- PROOF ---
  rw [show volume.restrict (Set.Ioc a b) = volume.restrict (Set.Ioo a b) from
    (Measure.restrict_congr_set Ioo_ae_eq_Ioc).symm]
  refine (stronglyMeasurable_derivWithin_Ici
    (fun r : ℝ => exp ((-r) • toRealMat sys.A) *ᵥ x r)).aestronglyMeasurable.congr ?_
  refine (ae_restrict_iff' measurableSet_Ioo).mpr (Filter.Eventually.of_forall fun s hs => ?_)
  exact (traj.aux_integrand_eq_derivWithin hT ⟨hs.1.le, hs.2⟩).symm

/-- The exponential is continuous, so it is bounded over a compact step. -/
theorem aux_classical_continuous_expNeg (A : Mat ℝ n n) : Continuous fun s : ℝ => exp ((-s) • A) :=
  exp_continuous.comp (continuous_neg.smul continuous_const)


-- =======================================  MAIN THEOREM  ======================================= --

/-- What `variation_of_constants` asks for, given only that the input set is
bounded — which every representation of a set of points is. -/
theorem LinearSys.IsCanonicalClassicalTrajectory.intervalIntegrable_input {sys : LinearSys 𝕋 n}
    {T : Set ℝ}
    {R₀ U : S n} {x u : ℝ → Vec ℝ n} {a b : ℝ}
    (traj : sys.IsCanonicalClassicalTrajectory T R₀ U x u)
    (hT : Set.Icc a b ⊆ T) (hab : a ≤ b) (hU : Bornology.IsBounded (construct U)) :
    IntervalIntegrable (fun s => exp ((-s) • toRealMat sys.A) *ᵥ u s)
      volume a b := by -- --- PROOF ---
  obtain ⟨CU, hCU⟩ := hU.exists_norm_le
  obtain ⟨CE, hCE⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    (aux_classical_continuous_expNeg (toRealMat sys.A)).continuousOn
  have hCE0 : 0 ≤ CE := le_trans (norm_nonneg _) (hCE a ⟨le_refl a, hab⟩)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine ⟨traj.aux_aestronglyMeasurable hT,
    HasFiniteIntegral.restrict_of_bounded (C := CE * CU) measure_Ioc_lt_top ?_⟩
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun s hs => ?_)
  calc ‖exp ((-s) • toRealMat sys.A) *ᵥ u s‖
      ≤ ‖exp ((-s) • toRealMat sys.A)‖ * ‖u s‖ := Matrix.linfty_opNorm_mulVec _ _
    _ ≤ CE * CU := mul_le_mul (hCE s ⟨hs.1.le, hs.2⟩)
        (hCU _ (traj.input s (hT ⟨hs.1.le, hs.2⟩))) (norm_nonneg _) hCE0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
