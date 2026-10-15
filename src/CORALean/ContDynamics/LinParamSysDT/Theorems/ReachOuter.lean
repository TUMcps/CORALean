module

public import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachOuterOn

@[expose] public section

/-!
# `LinParamSysDT.reach` contains every trajectory

`reach_outer` is the total case of `reach_outer_on`, `K := k` and `le_rfl` away
via `aux_toCanonicalTrajectoryOn`, so nothing here is proved twice.
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       06-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise ContSet Plus Reduce Mtimes

variable {n : ℕ} {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes 𝕄 S]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes 𝕄 S] in
/-- A total run restricted to its first `K` steps: nothing past step `K` is
used, so nothing past it needs to hold. -/
theorem LinParamSysDT.CanonicalTrajectory.aux_toCanonicalTrajectoryOn
    {sys : LinParamSysDT 𝕄 n} {R₀ U : S n} {x u : ℕ → Vec ℝ n}
    (traj : sys.CanonicalTrajectory R₀ U x u) (K : ℕ) :
    sys.CanonicalTrajectoryOn R₀ U K x u where
  init := traj.init
  input k _ := traj.input k
  step k _ := traj.step k


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinParamSysDT.reach_outer (sys : LinParamSysDT 𝕄 n) {o : ℕ} (ho : 0 < o) (R₀ U : S n)
    {x u : ℕ → Vec ℝ n} (traj : sys.CanonicalTrajectory R₀ U x u) (k : ℕ) :
    x k ∈ construct (sys.reach ⟨R₀, U, 0, k⟩ ⟨o, ho⟩) :=
  sys.reach_outer_on ho R₀ U (traj.aux_toCanonicalTrajectoryOn k) k le_rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
