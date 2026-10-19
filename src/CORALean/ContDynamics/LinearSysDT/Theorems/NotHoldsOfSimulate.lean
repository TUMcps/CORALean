module

public import CORALean.ContDynamics.LinearSysDT.Theorems.HoldsOfReach
public import CORALean.ContDynamics.LinearSysDT.Theorems.SimulateIsTrajectory

@[expose] public section

/-!
# One sampled run can falsify what reachability can only fail to prove

The contrapositive of `holds_of_reach` at `simulate_isTrajectory`: a specification
violated along one sampled run cannot have held on the reachable set either.
This is the point of simulation. An enclosure is a superset, so a specification
holding on it proves safety and one violated on it proves nothing — the
violation may sit entirely in the approximation error. A run is exact: one
point genuinely reached, so a specification it violates is genuinely violated.
Reachability and simulation answer opposite halves of the same question.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]
variable {ContSet : Type} [CORALean.ContSet ContSet (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.not_holds_of_simulate (sys : LinearSysDT 𝕋 n) {o : ℕ} (ho : 0 < o)
    (R₀ U : S n) (spec : Specification ContSet) {x₀ : Vec ℝ n} (hx₀ : x₀ ∈ construct R₀)
    {u : ℕ → Vec ℝ n} (hu : ∀ k, u k ∈ construct U) (k : ℕ)
    (hbad : ¬ spec.Holds {sys.simulate x₀ u k}) : -- --- STMT ---
    ¬ spec.Holds (construct (sys.reach ⟨R₀, U, 0, k⟩ ⟨o, ho⟩)) :=
  fun h => hbad (sys.holds_of_reach ho R₀ U spec (sys.simulate_isTrajectory hx₀ hu) k h)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
