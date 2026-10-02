import CORALean.ContDynamics.LinearSys.Theorems.ContinuousOnState
import CORALean.ContDynamics.LinearSys.Theorems.InputEqDerivWithin
import CORALean.ContDynamics.LinearSys.Theorems.MulVecL
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The input is measurable, with nothing assumed of it

`u` is measurable on any window the domain covers, with nothing assumed of it:
the derivative term is strongly measurable for every function, and the drift
is a continuous map of a continuous state. `InputSolutionTimeIntervalOuter`
composes this with `inputReach_mono`, and `InputSolutionTimeIntervalOuterSplit`
subtracts the piece before an intermediate time from it.
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

theorem LinearSys.Trajectory.aestronglyMeasurable_input {sys : LinearSys 𝕋 n} {T : Set ℝ}
    {R₀ U : S n} {x u : ℝ → Vec ℝ n} {a b : ℝ} (traj : sys.Trajectory T R₀ U x u)
    (hT : Set.Icc a b ⊆ T) :
    AEStronglyMeasurable u (volume.restrict (Set.Icc a b)) := by -- --- PROOF ---
  rw [show volume.restrict (Set.Icc a b) = volume.restrict (Set.Ioo a b) from
    (Measure.restrict_congr_set Ioo_ae_eq_Icc).symm]
  have hderiv : AEStronglyMeasurable (fun s : ℝ => derivWithin x (Set.Ici s) s)
      (volume.restrict (Set.Ioo a b)) :=
    (stronglyMeasurable_derivWithin_Ici x).aestronglyMeasurable
  have hstate : AEStronglyMeasurable x (volume.restrict (Set.Ioo a b)) :=
    (traj.continuousOn_state.mono fun s hs => hT ⟨hs.1.le, hs.2.le⟩).aestronglyMeasurable
      measurableSet_Ioo
  have hdrift : AEStronglyMeasurable (fun s : ℝ => toRealMat sys.A *ᵥ x s)
      (volume.restrict (Set.Ioo a b)) :=
    (mulVecL (toRealMat sys.A)).continuous.comp_aestronglyMeasurable hstate
  refine (hderiv.sub hdrift).congr ?_
  refine (ae_restrict_iff' measurableSet_Ioo).mpr (Filter.Eventually.of_forall fun s hs => ?_)
  exact (traj.input_eq_derivWithin hT ⟨hs.1.le, hs.2⟩).symm

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
