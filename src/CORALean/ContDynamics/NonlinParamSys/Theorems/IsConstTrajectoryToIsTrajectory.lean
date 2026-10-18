module

public import CORALean.ContDynamics.NonlinParamSys.NonlinParamSys

@[expose] public section

/-!
# A constant-parameter trajectory is a time-varying one

`IsConstTrajectory`'s fixed `p` read through the constant function `fun _ => p`:
same initial condition, same input condition, and `param` becomes trivial since
every `t` reads the same membership witness.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {n m q : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinParamSys.isConstTrajectory_toIsTrajectory {sys : NonlinParamSys n m q} {T : Set ℝ}
    {R₀ : S n} {U : S m} {P : S q} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} {p : Vec ℝ q}
    {y : ℝ → Vec ℝ sys.r} (traj : sys.IsConstTrajectory T R₀ U P x u p y) :
    sys.IsTrajectory T R₀ U P x u (fun _ => p) y where
  init := traj.init
  input := traj.input
  param _ _ := traj.param
  meas := traj.meas
  integrable := traj.integrable
  cont := traj.cont
  flow := traj.flow
  output := traj.output

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
