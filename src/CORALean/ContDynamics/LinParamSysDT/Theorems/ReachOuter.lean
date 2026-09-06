import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachOuterOn

/-!
# `LinParamSysDT.reach` contains every trajectory

`reach_outer` is the total case of `reach_outer_on`, `K := k` and `le_rfl` away
via `aux_toTrajectoryOn`, so nothing here is proved twice.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix Pointwise ContSet Plus Reduce Mtimes

variable {n : ℕ} {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes 𝕄 S]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes 𝕄 S] in
/-- A total run restricted to its first `K` steps: nothing past step `K` is
used, so nothing past it needs to hold. -/
theorem LinParamSysDT.Trajectory.aux_toTrajectoryOn {sys : LinParamSysDT 𝕄 n} {R₀ U : S n}
    {x u : ℕ → Vec ℝ n} (traj : sys.Trajectory R₀ U x u) (K : ℕ) :
    sys.TrajectoryOn R₀ U K x u where
  init := traj.init
  input k _ := traj.input k
  step k _ := traj.step k


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinParamSysDT.reach_outer (sys : LinParamSysDT 𝕄 n) (o : ℕ) (R₀ U : S n)
    {x u : ℕ → Vec ℝ n} (traj : sys.Trajectory R₀ U x u) (k : ℕ) :
    x k ∈ construct (sys.reach o R₀ U k) :=
  sys.reach_outer_on o R₀ U (traj.aux_toTrajectoryOn k) k le_rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
