import CORALean.ContDynamics.NonlinearSysDT.Theorems.ReachOuterOn

/-!
# `NonlinearSysDT.reach` contains every trajectory

The total case of `reach_outer_on`, `K := k` and `le_rfl` away via
`aux_toTrajectoryOn`, so nothing about a bounded run is proved twice.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [OfInterval S]

omit [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]
  [OfInterval S] in


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A total run restricted to its first `K` steps. -/
theorem NonlinearSysDT.Trajectory.aux_toTrajectoryOn {sys : NonlinearSysDT n m} {R₀ : S n}
    {U : S m} {x : ℕ → Vec ℝ n} {u : ℕ → Vec ℝ m}
    (traj : sys.Trajectory R₀ U x u) (K : ℕ) : sys.TrajectoryOn R₀ U K x u where
  init := traj.init
  input k _ := traj.input k
  step k _ := traj.step k


-- =======================================  MAIN THEOREM  ======================================= --

/-- `reach` contains every trajectory of the total run, at every step. -/
theorem NonlinearSysDT.reach_outer (sys : NonlinearSysDT n m) {U : S m} {o : ℕ} (ho : 0 < o)
    (steps : ℕ → sys.LinStep U) (R₀ : S n) {x : ℕ → Vec ℝ n} {u : ℕ → Vec ℝ m}
    (traj : sys.Trajectory R₀ U x u) (hR : ∀ k, x k ∈ (steps k).R) (k : ℕ) :
    x k ∈ construct (sys.reach o ho steps R₀ k) :=
  sys.reach_outer_on ho steps R₀ (traj.aux_toTrajectoryOn k) (fun i _ => hR i) k le_rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
