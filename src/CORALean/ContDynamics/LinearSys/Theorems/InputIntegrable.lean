import CORALean.ContDynamics.LinearSys.Theorems.AestronglyMeasurableInput
import CORALean.ContDynamics.LinearSys.Theorems.HasDerivWithinAtExpNegMulVec
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# What `variation_of_constants` assumes about the input, discharged

`meas` makes `u` measurable on the window, and `e^{-As}` is continuous, so
their product is measurable. Boundedness comes from outside, and from the input
set rather than from `u`: a bounded `U` bounds the integrand together with the
exponential, which is continuous over a compact step.

The statement asks only that the domain cover the window `[a, b]` it speaks
about.
-/

-- Authors:       Tobias Ladner
-- Written:       19-August-2026
-- Last update:   10-October-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The exponential is continuous, so it is bounded over a compact step. -/
theorem aux_continuous_expNeg (A : Mat ℝ n n) : Continuous fun s : ℝ => exp ((-s) • A) :=
  exp_continuous.comp (continuous_neg.smul continuous_const)

/-- A continuous matrix times the measurable input is measurable. -/
theorem LinearSys.Trajectory.aux_aestronglyMeasurable {sys : LinearSys 𝕋 n} {T : Set ℝ}
    {R₀ U : S n} {x u : ℝ → Vec ℝ n} {a b : ℝ} (traj : sys.Trajectory T R₀ U x u)
    (hT : Set.Icc a b ⊆ T) :
    AEStronglyMeasurable (fun s => exp ((-s) • toRealMat sys.A) *ᵥ u s)
      (volume.restrict (Set.Ioc a b)) :=
  (((aux_continuous_expNeg (toRealMat sys.A)).comp continuous_fst).matrix_mulVec
    continuous_snd).comp_aestronglyMeasurable₂ (f := fun s : ℝ => s) aestronglyMeasurable_id
    ((traj.aestronglyMeasurable_input hT).mono_measure
      (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl))


-- =======================================  MAIN THEOREM  ======================================= --

-- the integrand's bound is assembled from two witnesses, over the local norm instances
set_option maxHeartbeats 400000 in
/-- What `variation_of_constants` asks for, given only that the input set is
bounded — which every representation of a set of points is. -/
theorem LinearSys.Trajectory.intervalIntegrable_input {sys : LinearSys 𝕋 n} {T : Set ℝ}
    {R₀ U : S n} {x u : ℝ → Vec ℝ n} {a b : ℝ} (traj : sys.Trajectory T R₀ U x u)
    (hT : Set.Icc a b ⊆ T) (hab : a ≤ b) (hU : Bornology.IsBounded (construct U)) :
    IntervalIntegrable (fun s => exp ((-s) • toRealMat sys.A) *ᵥ u s)
      volume a b := by -- --- PROOF ---
  obtain ⟨CU, hCU⟩ := hU.exists_norm_le
  obtain ⟨CE, hCE⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    (aux_continuous_expNeg (toRealMat sys.A)).continuousOn
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
