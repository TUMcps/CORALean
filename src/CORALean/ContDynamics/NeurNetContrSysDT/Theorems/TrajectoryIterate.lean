import CORALean.ContDynamics.NeurNetContrSysDT.NeurNetContrSysDT

/-!
# A closed-loop run is an orbit

The controller is a function, so the loop is deterministic: every run is the
orbit of `map`, and every point of `R₀` starts one — so the runs of a closed
loop are exactly its initial states. Stated rather than left implied, because
it is what makes the reachability guarantee weaker than it looks — a set of
runs here is a set of initial states, and the enclosure is still loose,
`reach` pairing each state with every input rather than with its own.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]

/-- Every point of `R₀` starts a run, so the runs of a closed loop are exactly
its initial states. -/
theorem NeurNetContrSysDT.trajectory_iterate (sys : NeurNetContrSysDT 𝕋 S n) {R₀ : S n}
    {x₀ : Vec ℝ n} (hx₀ : x₀ ∈ construct R₀) :
    sys.Trajectory R₀ (fun k => sys.map^[k] x₀) where
  init := hx₀
  step k := Function.iterate_succ_apply' sys.map k x₀

end CORALean.Real
