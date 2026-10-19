module

public import CORALean.ContDynamics.NeurNetContrSysDT.Operations.Simulate
public import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.IsTrajectoryOfMap

@[expose] public section

/-!
# `simulate` samples a trajectory

`simulate v x₀` satisfies `IsTrajectory R₀ U_ext` whenever `x₀ ∈ construct R₀` and the external
input `v` stays in `U_ext`: `init` and `v` are the hypotheses handed in and `step` is `rfl`, since
`simulate` is `IsTrajectory.step`'s equation read as a recursive definition rather than a
predicate.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       06-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeurNetContrSysDT.simulate_isTrajectory (sys : NeurNetContrSysDT (LinearSysDT 𝕋 n) S n)
    (π : Vec ℝ n → Vec ℝ sys.m) {R₀ : S n} {U_ext : Set (Vec ℝ sys.nExt)}
    {W : Set (Vec ℝ sys.plant.r)} (hW : 0 ∈ W) {v : ℕ → Vec ℝ sys.nExt} (hv : ∀ k, v k ∈ U_ext)
    {x₀ : Vec ℝ n} (hx₀ : x₀ ∈ construct R₀) : -- --- STMT ---
    sys.IsTrajectory π R₀ U_ext W (sys.simulate π v x₀) v 0 :=
  NeurNetContrSysDT.isTrajectory_of_map hW hx₀ hv fun _ => rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
