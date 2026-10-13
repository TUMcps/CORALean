import CORALean.ContDynamics.NonlinearSysDT.Theorems.ReachOuter
import CORALean.ContDynamics.NonlinearSysDT.Theorems.SimulateTrajectory

/-!
# A sampled run stays inside the reachable set

`simulate_trajectory` handed to `reach_outer`, at whatever confinement
`reach_outer` itself asks for: a re-linearized step needs its own certified
region, and a sampled run supplies no shortcut around checking it stayed
there.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable {𝕋 : Type} [CORALean.Float.FloatOps 𝕋] [CORALean.Float.SoundFloatArithmetic 𝕋]
variable [Mtimes (Mat 𝕋) S] [CORALean.Float.OfInterval S 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearSysDT.simulate_mem_reach (sys : NonlinearSysDT n m) {U : S m} {o : ℕ}
    (ho : 0 < o) (steps : ℕ → sys.LinStep 𝕋 U) (R₀ : S n) {x₀ : Vec ℝ n} (hx₀ : x₀ ∈ construct R₀)
    {u : ℕ → Vec ℝ m} (hu : ∀ k, u k ∈ construct U)
    (hR : ∀ k, sys.simulate x₀ u k ∈ (steps k).R) (k : ℕ) :
    sys.simulate x₀ u k ∈ construct (sys.reach ⟨R₀, U, 0, k⟩ ⟨o, ho⟩ steps) :=
  sys.reach_outer ho steps R₀ (sys.simulate_trajectory hx₀ hu) hR k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
