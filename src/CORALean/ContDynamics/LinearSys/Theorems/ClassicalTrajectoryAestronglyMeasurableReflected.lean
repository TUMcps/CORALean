module

public import CORALean.ContDynamics.LinearSys.Theorems.InputEqDerivWithin
public import CORALean.ContDynamics.LinearSys.Theorems.MulVecL
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-!
# A classical run's input is measurable, in the reflected form a step needs

What `inputSolution_outer` asks of the input, in the reflected form the
substitution `τ = c - s` leaves behind. The reflected argument sweeps
`[c - r, c)`, so a domain covering the step ending at `c` is what it needs.
`CanonicalClassicalTrajectory.stepInput_outer` is the one caller. Kept for a classical run
on a window `[kΔt, (k+1)Δt]` that does not reach back to `0` — a nonlinear run
linearized step by step — where `CanonicalClassicalTrajectory.trajectory` cannot hand it to
`Trajectory`, whose integral equation is anchored at `0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-August-2026
-- Last update:   10-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar MeasureTheory

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.CanonicalClassicalTrajectory.aestronglyMeasurable_input_reflected
    {sys : LinearSys 𝕋 n} {T : Set ℝ} {R₀ U : S n} {x u : ℝ → Vec ℝ n}
    (traj : sys.CanonicalClassicalTrajectory T R₀ U x u) {c r : ℝ} (hT : Set.Icc (c - r) c ⊆ T) :
    AEStronglyMeasurable (fun τ => u (c - τ)) (volume.restrict (Set.Ioc 0 r)) := by -- --- PROOF ---
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
  have hxcont : ContinuousOn x T := fun t ht => (traj.flow t ht).continuousWithinAt
  have hstate : AEStronglyMeasurable (fun τ : ℝ => x (c - τ))
      (volume.restrict (Set.Ioc 0 r)) :=
    (hxcont.comp hrefl.continuousOn hmaps).aestronglyMeasurable
      measurableSet_Ioc
  have hdrift : AEStronglyMeasurable (fun τ : ℝ => toRealMat sys.A *ᵥ x (c - τ))
      (volume.restrict (Set.Ioc 0 r)) :=
    (mulVecL (toRealMat sys.A)).continuous.comp_aestronglyMeasurable hstate
  refine (hderiv.sub hdrift).congr ?_
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun τ hτ => ?_)
  exact (traj.input_eq_derivWithin hT (hmem τ hτ)).symm

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
