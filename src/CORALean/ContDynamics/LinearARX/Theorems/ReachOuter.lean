import CORALean.ContDynamics.LinearARX.Theorems.ToLinearSysDTTrajectory
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOuter

/-!
# The converted system's reach contains every ARX window

`LinearSysDT.reach_outer` along the converted trajectory: the window of outputs
`(y(k), …, y(k+p-1))` lies in the reachable set at step `k`. The set is the
conversion's, with its input set `inputSet U`; reach in the ARX form is separate.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   01-October-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar Plus Reduce Mtimes

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {dy du p : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearARX.reach_outer (sys : LinearARX 𝕋 dy du p) {o : ℕ} (ho : 0 < o)
    (Y₀ : S (p * dy)) (U : S du) {y : ℕ → Vec ℝ dy} {u : ℕ → Vec ℝ du}
    (traj : sys.Trajectory Y₀ U y u) (k : ℕ) :
    LinearARX.stack p y k ∈ construct
      (sys.toLinearSysDT.reach ⟨Y₀, sys.inputSet U, 0, k⟩ ⟨o, ho⟩) :=
  sys.toLinearSysDT.reach_outer ho Y₀ (sys.inputSet U) (sys.toLinearSysDT_trajectory traj) k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
