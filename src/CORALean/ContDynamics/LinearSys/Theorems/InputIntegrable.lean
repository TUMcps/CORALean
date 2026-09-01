import CORALean.ContDynamics.LinearSys.Theorems.VariationOfConstants

/-!
# What `variation_of_constants` assumes about the input, discharged

`Trajectory` puts no regularity on `u`, and none has to be added: the flow pins
`u` to the derivative of `x`, so the integrand `e^{-As} u(s)` is itself a
derivative — of `e^{-As} x(s)`. A derivative within `Ici s` is measurable in `s`
for *any* function, so measurability costs nothing.

Boundedness is the one thing that comes from outside, and from the input set
rather than from `u`: a bounded `U` bounds the integrand together with the
exponential, which is continuous over a compact step.

Measurability survives the reflection `τ ↦ c - τ` that `inputSolution_outer`
integrates against, the derivative term being strongly measurable rather than
merely almost-everywhere so.
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
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]

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

/-- Differentiable where the flow holds, hence continuous there. -/
theorem LinearSys.Trajectory.aux_continuousOn_state {sys : LinearSys 𝕋 n} {R₀ U : S n}
    {x u : ℝ → Vec ℝ n} (traj : sys.Trajectory R₀ U x u) : ContinuousOn x (Set.Ici 0) :=
  fun t ht => (traj.flow t ht).continuousWithinAt

/-- `u` as a derivative minus the drift. The flow states the sum; this is the
rearrangement that leaves `u` alone on one side, which is what carries
measurability to `u` itself rather than to the integrand. -/
theorem LinearSys.Trajectory.aux_input_eq_derivWithin {sys : LinearSys 𝕋 n} {R₀ U : S n}
    {x u : ℝ → Vec ℝ n} (traj : sys.Trajectory R₀ U x u) {t : ℝ} (ht : 0 ≤ t) :
    u t = derivWithin x (Set.Ici t) t - toRealMat sys.A *ᵥ x t := by
  rw [((traj.flow t ht).mono (Set.Ici_subset_Ici.mpr ht)).derivWithin
    (uniqueDiffWithinAt_Ici t)]
  abel

/-- `u` is measurable on any window inside `[0,∞)`, with nothing assumed of it:
the derivative term is strongly measurable for every function, and the drift is
a continuous map of a continuous state. -/
theorem LinearSys.Trajectory.aestronglyMeasurable_input {sys : LinearSys 𝕋 n} {R₀ U : S n}
    {x u : ℝ → Vec ℝ n} (traj : sys.Trajectory R₀ U x u) {a b : ℝ} (ha : 0 ≤ a) :
    AEStronglyMeasurable u (volume.restrict (Set.Icc a b)) := by
  have hderiv : AEStronglyMeasurable (fun s : ℝ => derivWithin x (Set.Ici s) s)
      (volume.restrict (Set.Icc a b)) :=
    (stronglyMeasurable_derivWithin_Ici x).aestronglyMeasurable
  have hstate : AEStronglyMeasurable x (volume.restrict (Set.Icc a b)) :=
    (traj.aux_continuousOn_state.mono fun s hs => le_trans ha hs.1).aestronglyMeasurable
      measurableSet_Icc
  have hdrift : AEStronglyMeasurable (fun s : ℝ => toRealMat sys.A *ᵥ x s)
      (volume.restrict (Set.Icc a b)) :=
    (mulVecL (toRealMat sys.A)).continuous.comp_aestronglyMeasurable hstate
  refine (hderiv.sub hdrift).congr ?_
  refine (ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall fun s hs => ?_)
  exact (traj.aux_input_eq_derivWithin (le_trans ha hs.1)).symm

/-- What `inputSolution_outer` asks of the input, in the reflected form the
substitution `τ = c - s` leaves behind. Nothing is assumed of `u`: the
derivative term is strongly measurable for every function and stays so through
`τ ↦ c - τ`, and the drift term is a continuous map of a continuous state.

`r ≤ c` keeps the reflected argument in `Ici 0`, which is the only place the
flow — and so the identity above — holds. -/
theorem LinearSys.Trajectory.aestronglyMeasurable_input_reflected {sys : LinearSys 𝕋 n}
    {R₀ U : S n} {x u : ℝ → Vec ℝ n} (traj : sys.Trajectory R₀ U x u) {c r : ℝ} (hrc : r ≤ c) :
    AEStronglyMeasurable (fun τ => u (c - τ)) (volume.restrict (Set.Ioc 0 r)) := by
  have hrefl : Continuous fun τ : ℝ => c - τ := continuous_const.sub continuous_id
  have hmaps : Set.MapsTo (fun τ : ℝ => c - τ) (Set.Ioc 0 r) (Set.Ici 0) := by
    intro τ hτ
    simp only [Set.mem_Ici, sub_nonneg]
    exact le_trans hτ.2 hrc
  have hderiv : AEStronglyMeasurable
      (fun τ : ℝ => derivWithin x (Set.Ici (c - τ)) (c - τ))
      (volume.restrict (Set.Ioc 0 r)) :=
    ((stronglyMeasurable_derivWithin_Ici x).comp_measurable
      hrefl.measurable).aestronglyMeasurable
  have hstate : AEStronglyMeasurable (fun τ : ℝ => x (c - τ))
      (volume.restrict (Set.Ioc 0 r)) :=
    (traj.aux_continuousOn_state.comp hrefl.continuousOn hmaps).aestronglyMeasurable
      measurableSet_Ioc
  have hdrift : AEStronglyMeasurable (fun τ : ℝ => toRealMat sys.A *ᵥ x (c - τ))
      (volume.restrict (Set.Ioc 0 r)) :=
    (mulVecL (toRealMat sys.A)).continuous.comp_aestronglyMeasurable hstate
  refine (hderiv.sub hdrift).congr ?_
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun τ hτ => ?_)
  exact (traj.aux_input_eq_derivWithin (sub_nonneg.mpr (le_trans hτ.2 hrc))).symm

end CORALean.Real
