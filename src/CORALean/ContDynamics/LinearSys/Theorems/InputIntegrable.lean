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

Every statement asks only that the domain cover the window it speaks about, so
the identity pinning `u` holds on the half-open window alone — enough, the
missing point being null.

Measurability survives the reflection `τ ↦ c - τ` that `inputSolution_outer`
integrates against, the derivative term being strongly measurable rather than
merely almost-everywhere so.
-/

-- Authors:       Tobias Ladner
-- Written:       19-August-2026
-- Last update:   02-September-2026
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]

/-- The integrand is the derivative of the substituted trajectory, taken within
`Ici s`: the form Mathlib's measurability lemma speaks about, and no weaker, the
two agreeing wherever the domain still extends to the right of `s`. -/
theorem LinearSys.Trajectory.aux_integrand_eq_derivWithin {sys : LinearSys 𝕋 n} {T : Set ℝ}
    {R₀ U : S n} {x u : ℝ → Vec ℝ n} (traj : sys.Trajectory T R₀ U x u) {a b s : ℝ}
    (hT : Set.Icc a b ⊆ T) (hs : s ∈ Set.Ico a b) :
    exp ((-s) • toRealMat sys.A) *ᵥ u s
      = derivWithin (fun r : ℝ => exp ((-r) • toRealMat sys.A) *ᵥ x r) (Set.Ici s) s :=
  ((hasDerivWithinAt_expNeg_mulVec (toRealMat sys.A) x u (Set.Ici s) s
    (traj.flow_Ici hT hs)).derivWithin (uniqueDiffWithinAt_Ici s)).symm

/-- Measurable with nothing assumed of `u`: `stronglyMeasurable_derivWithin_Ici`
holds for every function, and the integrand is a derivative of that shape almost
everywhere on the window. -/
theorem LinearSys.Trajectory.aux_aestronglyMeasurable {sys : LinearSys 𝕋 n} {T : Set ℝ}
    {R₀ U : S n} {x u : ℝ → Vec ℝ n} {a b : ℝ} (traj : sys.Trajectory T R₀ U x u)
    (hT : Set.Icc a b ⊆ T) :
    AEStronglyMeasurable (fun s => exp ((-s) • toRealMat sys.A) *ᵥ u s)
      (volume.restrict (Set.Ioc a b)) := by
  rw [show volume.restrict (Set.Ioc a b) = volume.restrict (Set.Ioo a b) from
    (Measure.restrict_congr_set Ioo_ae_eq_Ioc).symm]
  refine (stronglyMeasurable_derivWithin_Ici
    (fun r : ℝ => exp ((-r) • toRealMat sys.A) *ᵥ x r)).aestronglyMeasurable.congr ?_
  refine (ae_restrict_iff' measurableSet_Ioo).mpr (Filter.Eventually.of_forall fun s hs => ?_)
  exact (traj.aux_integrand_eq_derivWithin hT ⟨hs.1.le, hs.2⟩).symm

/-- The exponential is continuous, so it is bounded over a compact step. -/
theorem aux_continuous_expNeg (A : Mat ℝ n n) : Continuous fun s : ℝ => exp ((-s) • A) :=
  exp_continuous.comp (continuous_neg.smul continuous_const)

-- the integrand's bound is assembled from two witnesses, over the local norm instances
set_option maxHeartbeats 400000 in
/-- What `variation_of_constants` asks for, given only that the input set is
bounded — which every representation of a set of points is. -/
theorem LinearSys.Trajectory.intervalIntegrable_input {sys : LinearSys 𝕋 n} {T : Set ℝ}
    {R₀ U : S n} {x u : ℝ → Vec ℝ n} {a b : ℝ} (traj : sys.Trajectory T R₀ U x u)
    (hT : Set.Icc a b ⊆ T) (hab : a ≤ b) (hU : Bornology.IsBounded (construct U)) :
    IntervalIntegrable (fun s => exp ((-s) • toRealMat sys.A) *ᵥ u s) volume a b := by
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

/-- Differentiable where the flow holds, hence continuous there. -/
theorem LinearSys.Trajectory.aux_continuousOn_state {sys : LinearSys 𝕋 n} {T : Set ℝ}
    {R₀ U : S n} {x u : ℝ → Vec ℝ n} (traj : sys.Trajectory T R₀ U x u) : ContinuousOn x T :=
  fun t ht => (traj.flow t ht).continuousWithinAt

/-- `u` as a derivative minus the drift. The flow states the sum; this is the
rearrangement that leaves `u` alone on one side, which is what carries
measurability to `u` itself rather than to the integrand. -/
theorem LinearSys.Trajectory.aux_input_eq_derivWithin {sys : LinearSys 𝕋 n} {T : Set ℝ}
    {R₀ U : S n} {x u : ℝ → Vec ℝ n} (traj : sys.Trajectory T R₀ U x u) {a b t : ℝ}
    (hT : Set.Icc a b ⊆ T) (ht : t ∈ Set.Ico a b) :
    u t = derivWithin x (Set.Ici t) t - toRealMat sys.A *ᵥ x t := by
  rw [(traj.flow_Ici hT ht).derivWithin (uniqueDiffWithinAt_Ici t)]
  abel

/-- `u` is measurable on any window the domain covers, with nothing assumed of
it: the derivative term is strongly measurable for every function, and the drift
is a continuous map of a continuous state. -/
theorem LinearSys.Trajectory.aestronglyMeasurable_input {sys : LinearSys 𝕋 n} {T : Set ℝ}
    {R₀ U : S n} {x u : ℝ → Vec ℝ n} {a b : ℝ} (traj : sys.Trajectory T R₀ U x u)
    (hT : Set.Icc a b ⊆ T) :
    AEStronglyMeasurable u (volume.restrict (Set.Icc a b)) := by
  rw [show volume.restrict (Set.Icc a b) = volume.restrict (Set.Ioo a b) from
    (Measure.restrict_congr_set Ioo_ae_eq_Icc).symm]
  have hderiv : AEStronglyMeasurable (fun s : ℝ => derivWithin x (Set.Ici s) s)
      (volume.restrict (Set.Ioo a b)) :=
    (stronglyMeasurable_derivWithin_Ici x).aestronglyMeasurable
  have hstate : AEStronglyMeasurable x (volume.restrict (Set.Ioo a b)) :=
    (traj.aux_continuousOn_state.mono fun s hs => hT ⟨hs.1.le, hs.2.le⟩).aestronglyMeasurable
      measurableSet_Ioo
  have hdrift : AEStronglyMeasurable (fun s : ℝ => toRealMat sys.A *ᵥ x s)
      (volume.restrict (Set.Ioo a b)) :=
    (mulVecL (toRealMat sys.A)).continuous.comp_aestronglyMeasurable hstate
  refine (hderiv.sub hdrift).congr ?_
  refine (ae_restrict_iff' measurableSet_Ioo).mpr (Filter.Eventually.of_forall fun s hs => ?_)
  exact (traj.aux_input_eq_derivWithin hT ⟨hs.1.le, hs.2⟩).symm

/-- What `inputSolution_outer` asks of the input, in the reflected form the
substitution `τ = c - s` leaves behind. The reflected argument sweeps
`[c - r, c)`, so a domain covering the step ending at `c` is what it needs. -/
theorem LinearSys.Trajectory.aestronglyMeasurable_input_reflected {sys : LinearSys 𝕋 n}
    {T : Set ℝ} {R₀ U : S n} {x u : ℝ → Vec ℝ n} (traj : sys.Trajectory T R₀ U x u) {c r : ℝ}
    (hT : Set.Icc (c - r) c ⊆ T) :
    AEStronglyMeasurable (fun τ => u (c - τ)) (volume.restrict (Set.Ioc 0 r)) := by
  have hrefl : Continuous fun τ : ℝ => c - τ := continuous_const.sub continuous_id
  have hmem : ∀ τ ∈ Set.Ioc (0 : ℝ) r, c - τ ∈ Set.Ico (c - r) c :=
    fun _ hτ => ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
  have hmaps : Set.MapsTo (fun τ : ℝ => c - τ) (Set.Ioc 0 r) T :=
    fun τ hτ => hT ⟨(hmem τ hτ).1, (hmem τ hτ).2.le⟩
  -- both halves of `x' - Ax` survive the reflection: one strongly measurable, one continuous
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
  exact (traj.aux_input_eq_derivWithin hT (hmem τ hτ)).symm

end CORALean.Real
