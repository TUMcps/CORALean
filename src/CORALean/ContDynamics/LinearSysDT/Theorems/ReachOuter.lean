module

public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOuterOn

@[expose] public section

/-!
# `LinearSysDT.reach` contains every trajectory

`reach_outer` is the total case of `reach_outer_on`, `K := k` and `le_rfl` away
via `aux_toTrajectoryOn`, so nothing here is proved twice.
-/

-- Authors:       Claude Opus 5
-- Written:       18-August-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise ContSet Scalar Plus Reduce Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] in
/-- A total run restricted to its first `K` steps: nothing past step `K` is
used, so nothing past it needs to hold. -/
theorem LinearSysDT.Trajectory.aux_toTrajectoryOn {sys : LinearSysDT 𝕋 n} {R₀ U : S n}
    {x u : ℕ → Vec ℝ n} (traj : sys.Trajectory R₀ U x u) (K : ℕ) :
    sys.TrajectoryOn R₀ U K x u where
  init := traj.init
  input k _ := traj.input k
  step k _ := traj.step k


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.reach_outer (sys : LinearSysDT 𝕋 n) {o : ℕ} (ho : 0 < o) (R₀ U : S n)
    {x u : ℕ → Vec ℝ n} (traj : sys.Trajectory R₀ U x u) (k : ℕ) :
    x k ∈ construct (sys.reach ⟨R₀, U, 0, k⟩ ⟨o, ho⟩) :=
  sys.reach_outer_on ho R₀ U (traj.aux_toTrajectoryOn k) k le_rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
