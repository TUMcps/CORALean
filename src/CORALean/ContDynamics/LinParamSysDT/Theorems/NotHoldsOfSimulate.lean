module

public import CORALean.ContDynamics.LinParamSysDT.Theorems.HoldsOfReach
public import CORALean.ContDynamics.LinParamSysDT.Theorems.SimulateIsTrajectory

@[expose] public section

/-!
# One sampled run can falsify what reachability can only fail to prove

The contrapositive of `holds_of_reach` at `simulate_isTrajectory`, exactly
`LinearSysDT.not_holds_of_simulate`'s statement at a matrix chosen per step:
a specification violated along one sampled run cannot have held on the
reachable set either. An enclosure is a superset, so a specification holding
on it proves safety and one violated on it proves nothing — the violation may
sit entirely in the approximation error. A run is exact, so what it violates
is genuinely violated.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Plus Reduce Mtimes

variable {n : ℕ} {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes 𝕄 S]
variable {ContSet : Type} [CORALean.ContSet ContSet (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinParamSysDT.not_holds_of_simulate (sys : LinParamSysDT 𝕄 n) {o : ℕ} (ho : 0 < o)
    (R₀ U : S n) (spec : Specification ContSet) {A : ℕ → Mat ℝ n n}
    (hA : ∀ k, A k ∈ construct sys.A)
    {x₀ : Vec ℝ n} (hx₀ : x₀ ∈ construct R₀) {u : ℕ → Vec ℝ n} (hu : ∀ k, u k ∈ construct U)
    (k : ℕ) (hbad : ¬ spec.Holds {sys.simulate A x₀ u k}) : -- --- CONCL ---
    ¬ spec.Holds (construct (sys.reach ⟨R₀, U, 0, k⟩ ⟨o, ho⟩)) :=
  fun h => hbad (sys.holds_of_reach ho R₀ U spec (sys.simulate_isTrajectory hA hx₀ hu) k h)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
