import CORALean.Real.ContDynamics.LinearSys.Theorems.VariationOfConstants

/-!
# What `variation_of_constants` assumes about the input, discharged

`Trajectory` puts no regularity on `u`, and none has to be added: the flow pins
`u` to the derivative of `x`, so the whole integrand `e^{-As} u(s)` is itself a
derivative — of `e^{-As} x(s)`, by the substitution that proves the closed form.
A derivative within `Ici s` is measurable in `s` for *any* function whatsoever,
so measurability costs nothing.

Boundedness is the one thing that comes from outside, and it comes from the
input set rather than from `u`: `u s ∈ construct U`, so a bounded `U` bounds the
integrand together with the exponential, which is continuous over a compact
step. Representations supply that bound; `ContSet` does not ask for it.
-/

-- Authors:       Tobias Ladner
-- Written:       19-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) n]

set_option maxHeartbeats 10000 in
/-- The integrand is the derivative of the substituted trajectory. Taken within
`Ici s` rather than `Ici 0`, which is the form Mathlib's measurability lemma
speaks about, and no weaker here: the two agree for `s ≥ 0`. -/
theorem LinearSys.Trajectory.aux_integrand_eq_derivWithin {sys : LinearSys 𝕋 n} {R₀ U : S n}
    {x u : ℝ → Vec ℝ n} (traj : sys.Trajectory R₀ U x u) {s : ℝ} (hs : 0 ≤ s) :
    exp ((-s) • toRealMat sys.A) *ᵥ u s
      = derivWithin (fun r : ℝ => exp ((-r) • toRealMat sys.A) *ᵥ x r) (Set.Ici s) s :=
  ((hasDerivWithinAt_expNeg_mulVec (toRealMat sys.A) x u (Set.Ici s) s
    ((traj.flow s hs).mono (Set.Ici_subset_Ici.mpr hs))).derivWithin
      (uniqueDiffWithinAt_Ici s)).symm

set_option maxHeartbeats 10000 in
/-- Measurable with nothing assumed of `u`: `stronglyMeasurable_derivWithin_Ici`
holds for every function, and the integrand is a derivative of that shape. -/
theorem LinearSys.Trajectory.aux_aestronglyMeasurable {sys : LinearSys 𝕋 n} {R₀ U : S n}
    {x u : ℝ → Vec ℝ n} {a b : ℝ} (traj : sys.Trajectory R₀ U x u) (ha : 0 ≤ a) :
    AEStronglyMeasurable (fun s => exp ((-s) • toRealMat sys.A) *ᵥ u s)
      (volume.restrict (Set.Ioc a b)) := by
  refine (stronglyMeasurable_derivWithin_Ici
    (fun r : ℝ => exp ((-r) • toRealMat sys.A) *ᵥ x r)).aestronglyMeasurable.congr ?_
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun s hs => ?_)
  exact (traj.aux_integrand_eq_derivWithin (le_trans ha hs.1.le)).symm

set_option maxHeartbeats 10000 in
/-- The exponential is continuous, so it is bounded over a compact step. -/
theorem aux_continuous_expNeg (A : Mat ℝ n n) : Continuous fun s : ℝ => exp ((-s) • A) :=
  exp_continuous.comp (continuous_neg.smul continuous_const)

set_option maxHeartbeats 400000 in
/-- What `variation_of_constants` asks for, given only that the input set is
bounded — which every representation of a set of points is. -/
theorem LinearSys.Trajectory.intervalIntegrable_input {sys : LinearSys 𝕋 n} {R₀ U : S n}
    {x u : ℝ → Vec ℝ n} {a b : ℝ} (traj : sys.Trajectory R₀ U x u) (ha : 0 ≤ a) (hab : a ≤ b)
    (hU : Bornology.IsBounded (construct U)) :
    IntervalIntegrable (fun s => exp ((-s) • toRealMat sys.A) *ᵥ u s) volume a b := by
  obtain ⟨CU, hCU⟩ := hU.exists_norm_le
  obtain ⟨CE, hCE⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    (aux_continuous_expNeg (toRealMat sys.A)).continuousOn
  have hCE0 : 0 ≤ CE := le_trans (norm_nonneg _) (hCE a ⟨le_refl a, hab⟩)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine ⟨traj.aux_aestronglyMeasurable ha,
    HasFiniteIntegral.restrict_of_bounded (C := CE * CU) measure_Ioc_lt_top ?_⟩
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun s hs => ?_)
  calc ‖exp ((-s) • toRealMat sys.A) *ᵥ u s‖
      ≤ ‖exp ((-s) • toRealMat sys.A)‖ * ‖u s‖ := Matrix.linfty_opNorm_mulVec _ _
    _ ≤ CE * CU := mul_le_mul (hCE s ⟨hs.1.le, hs.2⟩)
        (hCU _ (traj.input s (le_trans ha hs.1.le))) (norm_nonneg _) hCE0

end CORALean.Real
