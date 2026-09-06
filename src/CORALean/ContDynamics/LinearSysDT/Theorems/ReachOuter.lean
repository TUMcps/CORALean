import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOuterOn

/-!
# `LinearSysDT.reach` contains every trajectory

`reach_outer` is the total case of `reach_outer_on`, `K := k` and `le_rfl` away
via `aux_toTrajectoryOn`, so nothing here is proved twice.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   04-September-2026
-- Last revision: ---

namespace CORALean.Real

open Matrix Pointwise ContSet Scalar Plus Reduce Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]

omit [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] in
/-- A total run restricted to its first `K` steps: nothing past step `K` is
used, so nothing past it needs to hold. -/
theorem LinearSysDT.Trajectory.aux_toTrajectoryOn {sys : LinearSysDT 𝕋 n} {R₀ U : S n}
    {x u : ℕ → Vec ℝ n} (traj : sys.Trajectory R₀ U x u) (K : ℕ) :
    sys.TrajectoryOn R₀ U K x u where
  init := traj.init
  input k _ := traj.input k
  step k _ := traj.step k

theorem LinearSysDT.reach_outer (sys : LinearSysDT 𝕋 n) (o : ℕ) (R₀ U : S n)
    {x u : ℕ → Vec ℝ n} (traj : sys.Trajectory R₀ U x u) (k : ℕ) :
    x k ∈ construct (sys.reach o R₀ U k) :=
  sys.reach_outer_on o R₀ U (traj.aux_toTrajectoryOn k) k le_rfl

end CORALean.Real
