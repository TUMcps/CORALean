module

public import CORALean.ContDynamics.NonlinearSys.NonlinearSys
public import Mathlib.Analysis.InnerProductSpace.Basic

@[expose] public section

/-!
# A nonlinear trajectory restricts to any smaller time domain

Every field of a Carathéodory run is a statement at the points of `T`, or a measurability on
`T`, so each survives on any `T' ⊆ T`. It is what lets `linearize` be applied to a run over all
forward time while asking for confinement on one step only: restrict first, linearize second.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet MeasureTheory

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every run on `T` is a run on any smaller domain. -/
theorem NonlinearSys.IsTrajectory.restrict {sys : NonlinearSys n m} {T T' : Set ℝ}
    {R₀ : S n} {U : S m} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} {y : ℝ → Vec ℝ sys.q}
    (traj : sys.IsTrajectory T R₀ U x u y) (hT : T' ⊆ T) :
    sys.IsTrajectory T' R₀ U x u y where
  init := traj.init
  input t ht := traj.input t (hT ht)
  meas := traj.meas.mono_measure (Measure.restrict_mono hT le_rfl)
  integrable t ht := traj.integrable t (hT ht)
  cont := traj.cont.mono hT
  flow t ht := traj.flow t (hT ht)
  output t ht := traj.output t (hT ht)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
