import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.HoldsOfReach
import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.SimulateTrajectory

/-!
# One sampled run can falsify what reachability can only fail to prove

The contrapositive of `holds_of_reach` at `simulate_trajectory`: a specification
violated along one sampled run cannot have held on the reachable set either.
This is the point of simulation. An enclosure is a superset, so a specification
holding on it proves safety and one violated on it proves nothing — the
violation may sit entirely in the approximation error. A run is exact: one
point genuinely reached, so a specification it violates is genuinely violated.
Reachability and simulation answer opposite halves of the same question.
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

theorem NeurNetContrSysDT.not_holds_of_simulate (sys : NeurNetContrSysDT 𝕋 S n) {o : ℕ}
    (ho : 0 < o) (R₀ : S n) (spec : Specification (Vec ℝ n)) {π : Vec ℝ n → Vec ℝ n}
    (hπ : sys.contr.Sound π) {x₀ : Vec ℝ n} (hx₀ : x₀ ∈ construct R₀)
    (k : ℕ) (hbad : ¬ spec.Holds {sys.simulate π x₀ k}) :
    ¬ spec.Holds (construct (sys.reach o ho R₀ k)) :=
  fun h => hbad (sys.holds_of_reach ho R₀ spec hπ (sys.simulate_trajectory π hx₀) k h)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
