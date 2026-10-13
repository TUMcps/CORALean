import CORALean.ContDynamics.NonlinearSys.NonlinearSys
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# A nonlinear trajectory restricts to any smaller time domain

`HasDerivWithinAt.mono`: a derivative within `T` is one within every `T' ⊆ T`. It
is what lets `linearize` be applied to a run over all forward time while asking
for confinement on one step only: restrict first, linearize second.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every run on `T` is a run on any smaller domain. -/
theorem NonlinearSys.Trajectory.restrict {sys : NonlinearSys n m} {T T' : Set ℝ}
    {R₀ : S n} {U : S m} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m}
    (traj : sys.Trajectory T R₀ U x u) (hT : T' ⊆ T) :
    sys.Trajectory T' R₀ U x u where
  init := traj.init
  input t ht := traj.input t (hT ht)
  flow t ht := (traj.flow t (hT ht)).mono hT

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
