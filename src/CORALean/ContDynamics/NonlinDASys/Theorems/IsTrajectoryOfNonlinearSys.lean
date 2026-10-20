module

public import CORALean.ContDynamics.NonlinDASys.Operations.Basic

@[expose] public section

/-!
# A trajectory of the reduced system is one of the differential-algebraic system

With `y t := h (x t) (u t)`, which `sound` makes satisfy the constraint. Together with
`TrajectoryToNonlinearSys` the elimination of `y` loses no run and adds none.

## Inputs
* `sys` – system
* `red` – reduced model
* `T` – time set
* `R₀` – initial set
* `U` – input set
* `x` – state trajectory
* `u` – input signal
* `z` – output signal

## Hypotheses
* `traj` – reduced-system trajectory

## Conclusion
* the run with the reduced algebraic variable is a DAE trajectory
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

theorem NonlinearSys.IsTrajectory.toNonlinDASys {sys : NonlinDASys n p m} (red : sys.ReducedModel)
    {T : Set ℝ} {R₀ : S n} {U : S m} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m}
    {z : ℝ → Vec ℝ sys.q} (traj : red.toNonlinearSys.IsTrajectory T R₀ U x u z) :
    sys.IsTrajectory T R₀ U x (fun t => red.h (x t) (u t)) u z where
  init := traj.init
  input := traj.input
  meas := traj.meas
  integrable := traj.integrable
  cont := traj.cont
  flow := traj.flow
  constraint _ _ := red.sound _ _
  output := traj.output

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
