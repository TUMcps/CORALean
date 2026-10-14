module

public import CORALean.ContDynamics.NonlinParamSys.Operations.ToNonlinParam

@[expose] public section

/-!
# A nonlinear system's trajectories are its embedding's

`sys.toNonlinParam.f` ignores `p`, so `traj.flow` already proves the field the
embedded system needs; only `param` is new, and needs `construct P` nonempty to
supply the constant parameter the embedded trajectory reads — a trajectory of
the embedded system needs some `p` to exist, which `sys.Trajectory` alone does
not provide.
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

theorem NonlinearSys.Trajectory.toNonlinParam {sys : NonlinearSys n m} {T : Set ℝ}
    {R₀ : S n} {U : S m} {P : S q} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m}
    (traj : sys.Trajectory T R₀ U x u) (hP : (construct P).Nonempty) :
    sys.toNonlinParam.Trajectory T R₀ U P x u (fun _ => hP.choose) where
  init := traj.init
  input := traj.input
  param _ _ := hP.choose_spec
  flow := traj.flow

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
