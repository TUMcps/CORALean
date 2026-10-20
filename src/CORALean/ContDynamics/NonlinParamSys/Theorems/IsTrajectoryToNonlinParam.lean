module

public import CORALean.ContDynamics.NonlinParamSys.Operations.ToNonlinParam

@[expose] public section

/-!
# A nonlinear system's trajectories are its embedding's

`sys.toNonlinParam.f` ignores `p`, so `traj.flow` already proves the field the
embedded system needs; only `param` is new, and needs `construct P` nonempty to
supply the constant parameter the embedded trajectory reads — a trajectory of
the embedded system needs some `p` to exist, which `sys.IsTrajectory` alone does
not provide.

## Inputs
* `sys` – nonlinear system
* `T` – time set
* `R₀` – initial set
* `U` – input set
* `P` – parameter set
* `x` – state trajectory
* `u` – input signal
* `y` – output signal

## Hypotheses
* `traj` – nonlinear trajectory
* `hP` – parameter set nonempty

## Conclusion
* the run is a trajectory of the embedded parametric system
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

theorem NonlinearSys.IsTrajectory.toNonlinParam {sys : NonlinearSys n m} {T : Set ℝ}
    {R₀ : S n} {U : S m} {P : S q} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m}
    {y : ℝ → Vec ℝ sys.q} (traj : sys.IsTrajectory T R₀ U x u y) (hP : (construct P).Nonempty) :
    sys.toNonlinParam.IsTrajectory T R₀ U P x u (fun _ => hP.choose) y where
  init := traj.init
  input := traj.input
  param _ _ := hP.choose_spec
  meas := traj.meas
  integrable := traj.integrable
  cont := traj.cont
  flow := traj.flow
  output := traj.output

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
