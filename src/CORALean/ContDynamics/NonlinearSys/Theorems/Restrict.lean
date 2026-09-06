import CORALean.ContDynamics.NonlinearSys.NonlinearSys

/-!
# A nonlinear trajectory restricts to any smaller time domain

`HasDerivWithinAt.mono` again, exactly as in `LinearSys.Trajectory.restrict`. It
is what lets `linearize` be applied to a run over all forward time while asking
for confinement on one step only: restrict first, linearize second.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

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

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
