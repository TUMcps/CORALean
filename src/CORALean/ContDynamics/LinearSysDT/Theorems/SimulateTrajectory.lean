import CORALean.ContDynamics.LinearSysDT.Operations

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

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.simulate_trajectory (sys : LinearSysDT 𝕋 n) {R₀ U : S n}
    {x₀ : Vec ℝ n} (hx₀ : x₀ ∈ construct R₀) {u : ℕ → Vec ℝ n}
    (hu : ∀ k, u k ∈ construct U) :
    sys.Trajectory R₀ U (sys.simulate x₀ u) u where
  init := hx₀
  input := hu
  step _ := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
