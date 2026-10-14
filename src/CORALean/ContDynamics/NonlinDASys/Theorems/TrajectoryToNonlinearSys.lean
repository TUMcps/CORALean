module

public import CORALean.ContDynamics.NonlinDASys.Operations.Basic
public import CORALean.ContDynamics.NonlinDASys.Theorems.Basic

@[expose] public section

/-!
# A trajectory of the differential-algebraic system is one of the reduced system

`y_eq` puts `y t` at `h (x t) (u t)`, so `f` at the trajectory is the reduced field at it,
and the other fields are unchanged.
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

theorem NonlinDASys.Trajectory.toNonlinearSys {sys : NonlinDASys n p m} (red : sys.ReducedModel)
    {T : Set ℝ} {R₀ : S n} {U : S m} {x : ℝ → Vec ℝ n} {y : ℝ → Vec ℝ p} {u : ℝ → Vec ℝ m}
    (traj : sys.Trajectory T R₀ U x y u) : red.toNonlinearSys.Trajectory T R₀ U x u where
  init := traj.init
  input := traj.input
  flow t ht := by
    have := traj.flow t ht
    rwa [traj.y_eq red ht] at this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
