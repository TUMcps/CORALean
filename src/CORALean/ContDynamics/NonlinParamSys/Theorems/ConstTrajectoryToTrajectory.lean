import CORALean.ContDynamics.NonlinParamSys.NonlinParamSys

/-!
# A constant-parameter trajectory is a time-varying one

`ConstTrajectory`'s fixed `p` read through the constant function `fun _ => p`:
same initial condition, same input condition, and `param` becomes trivial since
every `t` reads the same membership witness.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {n m q : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinParamSys.constTrajectory_toTrajectory {sys : NonlinParamSys n m q} {T : Set ℝ}
    {R₀ : S n} {U : S m} {P : S q} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} {p : Vec ℝ q}
    (traj : sys.ConstTrajectory T R₀ U P x u p) :
    sys.Trajectory T R₀ U P x u (fun _ => p) where
  init := traj.init
  input := traj.input
  param _ _ := traj.param
  flow := traj.flow

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
