module

public import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachOuter
public import CORALean.ContDynamics.LinParamSysDT.Theorems.SimulateIsTrajectory

@[expose] public section

/-!
# A sampled run stays inside the reachable set

`simulate_isTrajectory` handed to `reach_outer`: the one fact `simulate` is for,
stated once so nothing downstream redoes the induction on `reach`.

## Inputs
* `sys` – system
* `o` – maximum zonotope order
* `R₀` – initial set
* `U` – input set
* `A` – matrices chosen per step
* `x₀` – initial state
* `u` – inputs
* `k` – step

## Hypotheses
* `ho` – order positive
* `hA` – every chosen matrix lies in the set
* `hx₀` – start lies in `R₀`
* `hu` – inputs lie in `U`

## Conclusion
* the simulated state at step `k` lies in the reachable set
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


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinParamSysDT.simulate_mem_reach (sys : LinParamSysDT 𝕄 n) {o : ℕ} (ho : 0 < o)
    (R₀ U : S n) {A : ℕ → Mat ℝ n n} (hA : ∀ k, A k ∈ construct sys.A) {x₀ : Vec ℝ n}
    (hx₀ : x₀ ∈ construct R₀) {u : ℕ → Vec ℝ n} (hu : ∀ k, u k ∈ construct U) (k : ℕ) :
    sys.simulate A x₀ u k ∈ construct (sys.reach ⟨R₀, U, 0, k⟩ ⟨o, ho⟩) :=
  sys.reach_outer ho R₀ U (sys.simulate_isTrajectory hA hx₀ hu) k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
