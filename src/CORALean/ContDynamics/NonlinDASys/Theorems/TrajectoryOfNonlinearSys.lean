module

public import CORALean.ContDynamics.NonlinDASys.Operations.Basic

@[expose] public section

/-!
# A trajectory of the reduced system is one of the differential-algebraic system

With `y t := h (x t) (u t)`, which `sound` makes satisfy the constraint. Together with
`TrajectoryToNonlinearSys` the elimination of `y` loses no run and adds none.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {n p m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearSys.Trajectory.toNonlinDASys {sys : NonlinDASys n p m} (red : sys.ReducedModel)
    {T : Set ℝ} {R₀ : S n} {U : S m} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m}
    (traj : red.toNonlinearSys.Trajectory T R₀ U x u) :
    sys.Trajectory T R₀ U x (fun t => red.h (x t) (u t)) u where
  init := traj.init
  input := traj.input
  flow := traj.flow
  constraint _ _ := red.sound _ _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
