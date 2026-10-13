module

public import CORALean.ContDynamics.NeurNetContrSysDT.Operations.Reach
public import CORALean.ContDynamics.NeurNetContrSysDT.Operations.Simulate

@[expose] public section

/-!
# `simulate` samples a trajectory

`simulate x₀` satisfies `Trajectory R₀` whenever `x₀ ∈ construct R₀`: `init` is
the hypothesis handed in and `step` is `rfl`, since `simulate` is
`Trajectory.step`'s equation read as a recursive definition rather than a
predicate. Two obligations, not three: the controller supplies the input, so a
run is determined by its initial state alone, with nothing for `input` to say.
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

theorem NeurNetContrSysDT.simulate_trajectory (sys : NeurNetContrSysDT 𝕋 S n)
    (π : Vec ℝ n → Vec ℝ n) {R₀ : S n}
    {x₀ : Vec ℝ n} (hx₀ : x₀ ∈ construct R₀) :
    sys.Trajectory π R₀ (sys.simulate π x₀) where
  init := hx₀
  step _ := rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
