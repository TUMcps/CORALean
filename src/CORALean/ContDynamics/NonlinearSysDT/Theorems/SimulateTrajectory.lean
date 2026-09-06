import CORALean.ContDynamics.NonlinearSysDT.Operations

/-!
# `simulate` samples a trajectory

`simulate x₀ u` satisfies `Trajectory R₀ U` whenever `x₀ ∈ construct R₀` and
`u` stays in `construct U` at every step: `init` and `input` are the
hypotheses handed in, `step` is `rfl`, since `simulate` is `Trajectory.step`'s
equation read as a recursive definition rather than as a predicate.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearSysDT.simulate_trajectory (sys : NonlinearSysDT n m) {R₀ : S n} {U : S m}
    {x₀ : Vec ℝ n} (hx₀ : x₀ ∈ construct R₀) {u : ℕ → Vec ℝ m}
    (hu : ∀ k, u k ∈ construct U) :
    sys.Trajectory R₀ U (sys.simulate x₀ u) u where
  init := hx₀
  input := hu
  step _ := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
