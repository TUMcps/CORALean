module

public import CORALean.ContDynamics.LinearSysDT.Operations.Simulate

@[expose] public section

/-!
# `simulate` samples a trajectory

`simulate x₀ u` satisfies `IsTrajectory R₀ U` whenever `x₀ ∈ construct R₀` and
`u` stays in `construct U` at every step: `init` and `input` are the
hypotheses handed in, `step` is `rfl`, since `simulate` is `IsTrajectory.step`'s
equation read as a recursive definition rather than as a predicate.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.simulate_isTrajectory (sys : LinearSysDT 𝕋 n) {R₀ U : S n}
    {x₀ : Vec ℝ n} (hx₀ : x₀ ∈ construct R₀) {u : ℕ → Vec ℝ n}
    (hu : ∀ k, u k ∈ construct U) :
    sys.IsCanonicalTrajectory R₀ U (sys.simulate x₀ u) u where
  init := hx₀
  input := hu
  step _ := rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
