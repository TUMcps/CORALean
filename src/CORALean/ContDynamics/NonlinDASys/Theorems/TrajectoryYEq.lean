import CORALean.ContDynamics.NonlinDASys.Operations.ToNonlinearSys

/-!
# The algebraic variable of a trajectory is `h` of its state and input

The constraint and `unique`: the only solution of `g(x, ·, u) = 0` is `h x u`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {n p m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinDASys.Trajectory.y_eq {sys : NonlinDASys n p m} (red : sys.ReducedModel)
    {T : Set ℝ} {R₀ : S n} {U : S m} {x : ℝ → Vec ℝ n} {y : ℝ → Vec ℝ p} {u : ℝ → Vec ℝ m}
    (traj : sys.Trajectory T R₀ U x y u) {t : ℝ} (ht : t ∈ T) : y t = red.h (x t) (u t) :=
  red.unique _ _ _ (traj.constraint t ht)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
