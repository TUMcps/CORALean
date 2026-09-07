import CORALean.ContDynamics.NonlinearSysDT.Theorems.ReachOuter
import CORALean.ContDynamics.NonlinearSysDT.Theorems.SimulateTrajectory

/-!
# A sampled run stays inside the reachable set

`simulate_trajectory` handed to `reach_outer`, at whatever confinement
`reach_outer` itself asks for: a re-linearized step needs its own certified
region, and a sampled run supplies no shortcut around checking it stayed
there.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [OfInterval S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearSysDT.simulate_mem_reach (sys : NonlinearSysDT n m) {U : S m} {o : ℕ}
    (ho : 0 < o) (steps : ℕ → sys.LinStep U) (R₀ : S n) {x₀ : Vec ℝ n} (hx₀ : x₀ ∈ construct R₀)
    {u : ℕ → Vec ℝ m} (hu : ∀ k, u k ∈ construct U)
    (hR : ∀ k, sys.simulate x₀ u k ∈ (steps k).R) (k : ℕ) :
    sys.simulate x₀ u k ∈ construct (sys.reach o ho steps R₀ k) :=
  sys.reach_outer ho steps R₀ (sys.simulate_trajectory hx₀ hu) hR k

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
