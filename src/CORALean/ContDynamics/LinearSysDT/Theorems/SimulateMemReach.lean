module

public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOuter
public import CORALean.ContDynamics.LinearSysDT.Theorems.SimulateTrajectory

@[expose] public section

/-!
# A sampled run stays inside the reachable set

`simulate_trajectory` handed to `reach_outer`: the one fact `simulate` is for,
stated once so nothing downstream redoes the induction on `reach`.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   30-September-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.simulate_mem_reach (sys : LinearSysDT 𝕋 n) {o : ℕ} (ho : 0 < o) (R₀ U : S n)
    {x₀ : Vec ℝ n} (hx₀ : x₀ ∈ construct R₀) {u : ℕ → Vec ℝ n}
    (hu : ∀ k, u k ∈ construct U) (k : ℕ) :
    sys.simulate x₀ u k ∈ construct (sys.reach ⟨R₀, U, 0, k⟩ ⟨o, ho⟩) :=
  sys.reach_outer ho R₀ U (sys.simulate_trajectory hx₀ hu) k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
