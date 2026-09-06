import CORALean.NN.Operations.RefinementConvergent
import CORALean.NN.Theorems.LinearExact

/-!
# The linear layer converges, at every level

`Layer.refinable` is what puts a layer with nothing to spend into a refinable
network, and `Convergent` then has to be met by its single enclosure. It is,
because that enclosure is exact: level `0` already lands the propagated set on
the image, and the inflation is spent on nothing.

So the linear layer contributes no residual at all to `PropagateAtInflate`'s
budget, and everything the schedule buys is bought at the activations — which
is the division of labour the refinement loop assumes [1].

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix Pointwise ContSet

variable {n m : ℕ}

theorem Layer.linear_refinable_convergent (W : Mat ℝ m n) (b : Vec ℝ m) :
    (Layer.linear (S := 𝒫𝒵) W b).refinable.Convergent := by
  intro s ε hε
  refine ⟨0, ?_⟩
  show construct ((Layer.linear (S := 𝒫𝒵) W b).propagate s)
      ⊆ (Layer.linear (S := 𝒫𝒵) W b).eval '' construct s + Metric.closedBall 0 ε
  rw [Layer.linear_exact]
  intro y hy
  -- the propagated set is the image already, so the ball contributes zero
  have h0 : (0 : Vec ℝ m) ∈ Metric.closedBall (0 : Vec ℝ m) ε := by
    rw [Metric.mem_closedBall, dist_self]
    exact hε.le
  have hmem := Set.add_mem_add hy h0
  rwa [add_zero] at hmem

end CORALean.Real
