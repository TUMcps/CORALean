module

public import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.TrajectoryOfMap

@[expose] public section

/-!
# A closed-loop run is an orbit

The controller is a function, so the loop is deterministic: every run is the
orbit of `map`, and every point of `R₀` starts one — so the runs of a closed
loop are exactly its initial states. Stated rather than left implied, because
it is what makes the reachability guarantee weaker than it looks — a set of
runs here is a set of initial states, and the enclosure is still loose,
`reach` pairing each state with every input rather than with its own.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every point of `R₀` starts a run, so the runs of a closed loop are exactly
its initial states. -/
theorem NeurNetContrSysDT.trajectory_iterate (sys : NeurNetContrSysDT (LinearSysDT 𝕋 n) S n)
    (π : Vec ℝ n → Vec ℝ sys.plant.m) {R₀ : S n} {W : Set (Vec ℝ sys.plant.r)} (hW : 0 ∈ W)
    {x₀ : Vec ℝ n} (hx₀ : x₀ ∈ construct R₀) :
    sys.Trajectory π R₀ W (fun k => (sys.map π)^[k] x₀) 0 :=
  NeurNetContrSysDT.trajectory_of_map hW hx₀ fun k => Function.iterate_succ_apply' (sys.map π) k x₀

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
