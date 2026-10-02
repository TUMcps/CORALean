import CORALean.ContDynamics.LinearSys.Theorems.ContinuousOnState
import CORALean.ContDynamics.LinearSys.Theorems.InputEqDerivWithin
import CORALean.ContDynamics.LinearSys.Theorems.MulVecL
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The input is measurable, in the reflected form a step needs

What `inputSolution_outer` asks of the input, in the reflected form the
substitution `τ = c - s` leaves behind. The reflected argument sweeps
`[c - r, c)`, so a domain covering the step ending at `c` is what it needs.
`StepInputOuter` is the one caller, matching `stepInput`'s own reflection.
-/

-- Authors:       Tobias Ladner
-- Written:       19-August-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar MeasureTheory

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.Trajectory.aestronglyMeasurable_input_reflected {sys : LinearSys 𝕋 n}
    {T : Set ℝ} {R₀ U : S n} {x u : ℝ → Vec ℝ n} (traj : sys.Trajectory T R₀ U x u) {c r : ℝ}
    (hT : Set.Icc (c - r) c ⊆ T) :
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
  have hstate : AEStronglyMeasurable (fun τ : ℝ => x (c - τ))
      (volume.restrict (Set.Ioc 0 r)) :=
    (traj.continuousOn_state.comp hrefl.continuousOn hmaps).aestronglyMeasurable
      measurableSet_Ioc
  have hdrift : AEStronglyMeasurable (fun τ : ℝ => toRealMat sys.A *ᵥ x (c - τ))
      (volume.restrict (Set.Ioc 0 r)) :=
    (mulVecL (toRealMat sys.A)).continuous.comp_aestronglyMeasurable hstate
  refine (hderiv.sub hdrift).congr ?_
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun τ hτ => ?_)
  exact (traj.input_eq_derivWithin hT (hmem τ hτ)).symm

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
