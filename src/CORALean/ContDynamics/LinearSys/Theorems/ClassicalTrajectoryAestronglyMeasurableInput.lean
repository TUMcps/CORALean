module

public import CORALean.ContDynamics.LinearSys.Theorems.InputEqDerivWithin
public import CORALean.ContDynamics.LinearSys.Theorems.MulVecL
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-!
# A classical run's input is measurable, with nothing assumed of it

A run with a derivative everywhere pins `u = ẋ - A x` on any window the domain
covers, and both terms are measurable for every function: the derivative within
`Ici s` is strongly measurable outright, the drift a continuous map of a
continuous state. So the derivative reading admits measurable inputs only, and a
set that quantifies over every admissible input signal — the backward sets of
`BackReachSetForallExists` — degenerates under it, which is why those are stated
over Carathéodory runs. `NonlinearSys` reads it off a classically linearized run.
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

theorem LinearSys.CanonicalClassicalTrajectory.aestronglyMeasurable_input {sys : LinearSys 𝕋 n}
    {T : Set ℝ} {R₀ U : S n} {x u : ℝ → Vec ℝ n} {a b : ℝ}
    (traj : sys.CanonicalClassicalTrajectory T R₀ U x u) (hT : Set.Icc a b ⊆ T) :
    AEStronglyMeasurable u (volume.restrict (Set.Icc a b)) := by -- --- PROOF ---
  rw [show volume.restrict (Set.Icc a b) = volume.restrict (Set.Ioo a b) from
    (Measure.restrict_congr_set Ioo_ae_eq_Icc).symm]
  have hderiv : AEStronglyMeasurable (fun s : ℝ => derivWithin x (Set.Ici s) s)
      (volume.restrict (Set.Ioo a b)) :=
    (stronglyMeasurable_derivWithin_Ici x).aestronglyMeasurable
  have hxcont : ContinuousOn x T := fun t ht => (traj.flow t ht).continuousWithinAt
  have hstate : AEStronglyMeasurable x (volume.restrict (Set.Ioo a b)) :=
    (hxcont.mono fun s hs => hT ⟨hs.1.le, hs.2.le⟩).aestronglyMeasurable measurableSet_Ioo
  have hdrift : AEStronglyMeasurable (fun s : ℝ => toRealMat sys.A *ᵥ x s)
      (volume.restrict (Set.Ioo a b)) :=
    (mulVecL (toRealMat sys.A)).continuous.comp_aestronglyMeasurable hstate
  refine (hderiv.sub hdrift).congr ?_
  refine (ae_restrict_iff' measurableSet_Ioo).mpr (Filter.Eventually.of_forall fun s hs => ?_)
  exact (traj.input_eq_derivWithin hT ⟨hs.1.le, hs.2⟩).symm

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
