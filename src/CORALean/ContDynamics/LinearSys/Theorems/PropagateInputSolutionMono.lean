import CORALean.ContDynamics.LinearSys.Operations.PropagateInputSolution

/-!
# The propagation preserves an enclosure of the one-step set

An induction over the step index, each step a Minkowski sum of a monotone image
with the set so far. It is what carries the three-way sandwich
`inner ⊆ exact ⊆ outer` of [1, Prop. 1] from one step to the horizon, so that
the proposition's Hausdorff bounds only ever have to be proved over a step.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed
      Continuous-Time Linear Systems Using Set Propagation". arXiv:2310.19083,
      2023.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A one-step enclosure is an enclosure after any number of steps. -/
theorem LinearSys.propagateInputSolution_mono (sys : LinearSys 𝕋 n) (Δt : ℝ)
    {Z Z' : Set (Vec ℝ n)} (h : Z ⊆ Z') (ω : ℕ) :
    sys.propagateInputSolution Δt Z ω ⊆ sys.propagateInputSolution Δt Z' ω := by
  induction ω with
  | zero => exact subset_rfl
  | succ k ih =>
    exact Set.add_subset_add ih (Set.image_mono h)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
