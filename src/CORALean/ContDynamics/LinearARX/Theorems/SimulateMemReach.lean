import CORALean.ContDynamics.LinearARX.Theorems.ReachOuter
import CORALean.ContDynamics.LinearARX.Theorems.SimulateTrajectory

/-!
# A simulated window lies in the reach set

`simulate_trajectory` composed with `reach_outer`: the window of simulated outputs
`(y(k), …, y(k+p-1))` lies in the reachable set at step `k`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar Plus Reduce Mtimes

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {dy du p : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearARX.simulate_mem_reach (sys : LinearARX 𝕋 dy du p) {o : ℕ} (ho : 0 < o)
    (Y₀ : S (p * dy)) (U : S du) {y₀ : Vec ℝ (p * dy)} (hy₀ : y₀ ∈ construct Y₀)
    {u : ℕ → Vec ℝ du} (hu : ∀ k, u k ∈ construct U) (k : ℕ) :
    LinearARX.stack p (sys.simulate y₀ u) k ∈ construct
      (sys.toLinearSysDT.reach ⟨Y₀, sys.inputSet U, 0, k⟩ ⟨o, ho⟩) :=
  sys.reach_outer ho Y₀ U (sys.simulate_trajectory hy₀ hu) k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
