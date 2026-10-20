module

public import CORALean.ContDynamics.NonlinearSysDT.Operations.Linearize
public import CORALean.ContDynamics.NonlinearSysDT.Operations.LinInput
public import CORALean.ContDynamics.NonlinearSysDT.Operations.Reach
public import CORALean.ContDynamics.NonlinearSysDT.Operations.Simulate

@[expose] public section

/-!
# `simulate` samples a trajectory

`simulate x₀ u` satisfies `IsTrajectory R₀ U` whenever `x₀ ∈ construct R₀` and
`u` stays in `construct U` at every step: `init` and `input` are the
hypotheses handed in, `step` is `rfl`, since `simulate` is `IsTrajectory.step`'s
equation read as a recursive definition rather than as a predicate.

## Inputs
* `sys` – system
* `R₀` – initial set
* `U` – input set
* `x₀` – start state
* `u` – input signal

## Hypotheses
* `hx₀` – start state in initial set
* `hu` – inputs in input set

## Conclusion
* the sampled run is a trajectory of the system
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearSysDT.simulate_isTrajectory (sys : NonlinearSysDT n m) {R₀ : S n} {U : S m}
    {x₀ : Vec ℝ n} (hx₀ : x₀ ∈ construct R₀) {u : ℕ → Vec ℝ m}
    (hu : ∀ k, u k ∈ construct U) :
    sys.IsTrajectory R₀ U (sys.simulate x₀ u) u (fun k => sys.g (sys.simulate x₀ u k) (u k)) where
  init := hx₀
  input := hu
  step _ := rfl
  output _ := rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
