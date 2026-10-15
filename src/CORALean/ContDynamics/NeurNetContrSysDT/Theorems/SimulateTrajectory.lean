module

public import CORALean.ContDynamics.NeurNetContrSysDT.Operations.Simulate
public import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.TrajectoryOfMap

@[expose] public section

/-!
# `simulate` samples a trajectory

`simulate x₀` satisfies `Trajectory R₀` whenever `x₀ ∈ construct R₀`: `init` is
the hypothesis handed in and `step` is `rfl`, since `simulate` is
`Trajectory.step`'s equation read as a recursive definition rather than a
predicate. Two obligations, not three: the controller supplies the input, so a
run is determined by its initial state alone, with nothing for `input` to say.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeurNetContrSysDT.simulate_trajectory (sys : NeurNetContrSysDT (LinearSysDT 𝕋 n) S n)
    (π : Vec ℝ n → Vec ℝ sys.plant.m) {R₀ : S n} {W : Set (Vec ℝ sys.plant.r)} (hW : 0 ∈ W)
    {x₀ : Vec ℝ n} (hx₀ : x₀ ∈ construct R₀) :
    sys.Trajectory π R₀ W (sys.simulate π x₀) 0 :=
  NeurNetContrSysDT.trajectory_of_map hW hx₀ fun _ => rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
