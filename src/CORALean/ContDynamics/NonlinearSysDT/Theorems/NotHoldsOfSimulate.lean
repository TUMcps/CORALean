import CORALean.ContDynamics.NonlinearSysDT.Theorems.HoldsOfReach
import CORALean.ContDynamics.NonlinearSysDT.Theorems.SimulateTrajectory

/-!
# One sampled run can falsify what reachability can only fail to prove

The contrapositive of `holds_of_reach` at `simulate_trajectory`, exactly
`LinearSysDT.not_holds_of_simulate`'s statement at a re-linearized step: a
specification violated along one sampled run cannot have held on the
reachable set either. Confinement (`hR`) is asked of `simulate` itself, as
`simulate_mem_reach` already asks it — no shortcut around checking a sampled
run stayed in the region each step's certificate was issued for.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
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

theorem NonlinearSysDT.not_holds_of_simulate (sys : NonlinearSysDT n m) {U : S m} (o : ℕ)
    (steps : ℕ → sys.LinStep U) (R₀ : S n) (spec : Specification (Vec ℝ n))
    {x₀ : Vec ℝ n} (hx₀ : x₀ ∈ construct R₀) {u : ℕ → Vec ℝ m} (hu : ∀ k, u k ∈ construct U)
    (hR : ∀ k, sys.simulate x₀ u k ∈ (steps k).R) (k : ℕ)
    (hbad : ¬ spec.Holds {sys.simulate x₀ u k}) :
    ¬ spec.Holds (construct (sys.reach o steps R₀ k)) :=
  fun h => hbad (sys.holds_of_reach o steps R₀ spec (sys.simulate_trajectory hx₀ hu) hR k h)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
