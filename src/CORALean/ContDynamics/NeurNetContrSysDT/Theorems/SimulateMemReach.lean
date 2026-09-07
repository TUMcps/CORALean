import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.ReachOuter
import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.SimulateTrajectory

/-!
# A sampled run stays inside the reachable set

`simulate_trajectory` handed to `reach_outer`: the one fact `simulate` is for,
stated once so nothing downstream redoes the induction on `reach`.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeurNetContrSysDT.simulate_mem_reach (sys : NeurNetContrSysDT 𝕋 S n) {o : ℕ} (ho : 0 < o)
    (R₀ : S n) {π : Vec ℝ n → Vec ℝ n} (hπ : sys.contr.Sound π)
    {x₀ : Vec ℝ n} (hx₀ : x₀ ∈ construct R₀) (k : ℕ) :
    sys.simulate π x₀ k ∈ construct (sys.reach o ho R₀ k) :=
  sys.reach_outer ho R₀ hπ (sys.simulate_trajectory π hx₀) k

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
