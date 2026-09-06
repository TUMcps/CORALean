import CORALean.NN.Layers.SigmoidLinearSigmoid
import CORALean.NN.Theorems.ActivationLipschitz
import CORALean.NN.Theorems.EvalLipschitz
import CORALean.NN.Theorems.LinearConvergent
import CORALean.NN.Theorems.LinearLipschitz
import CORALean.NN.Theorems.PropagateAtInflate
import CORALean.NN.Theorems.SigmoidLipschitz

/-!
# The network statement, at a network with three layers

`SigmoidRefinementConverges` discharges `Convergent` where the tail is empty and
its Lipschitz constant is `LipschitzWith.id`. Here neither is free: the head
activation's residual passes through a matrix and a second activation before it
reaches the output, so the tail bound is a product of two real constants and the
`K` in `PropagateAtInflate` is what the refinement level is divided by.

The linear layer meets `Convergent` at level `0` and every other level, its
propagation being exact — so the schedule spends its levels on the two
activations, and the middle layer only rescales what they leave — the division
of labour the loop assumes [1].

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Pointwise ContSet

variable {n m : ℕ}

theorem sigmoidLinearSigmoidNetwork_convergent (W : Mat ℝ m n) (b : Vec ℝ m) :
    (sigmoidLinearSigmoidNetwork W b).Convergent := by
  -- the last activation on its own, which is where the tail bound bottoms out
  have h₂ : (RefinableNetwork.cons (S := 𝒫𝒵)
      (Layer.activationPolyRefinable (n := m) sigmoidPolyFamily) .nil).LipschitzLayers :=
    ⟨⟨1, Layer.lipschitzWith_activation_eval lipschitzWith_sigmoid m⟩, trivial⟩
  -- and the matrix in front of it, whose constant is its largest row sum
  have h₁ : (RefinableNetwork.cons (S := 𝒫𝒵) (Layer.linear W b).refinable
      (.cons (Layer.activationPolyRefinable (n := m) sigmoidPolyFamily) .nil)).LipschitzLayers :=
    ⟨⟨_, Layer.lipschitzWith_linear_eval W b⟩, h₂⟩
  exact ⟨Layer.activationPolySigmoid_convergent n,
    RefinableNetwork.exists_lipschitzWith_eval _ h₁,
    Layer.linear_refinable_convergent W b,
    RefinableNetwork.exists_lipschitzWith_eval _ h₂,
    Layer.activationPolySigmoid_convergent m, ⟨1, LipschitzWith.id⟩, trivial⟩

/-- The loop converges on a genuine chain: some schedule is inside any inflation
of the exact output set, which with `propagateAt_outer` squeezes the enclosure
onto it. -/
theorem exists_schedule_sigmoidLinearSigmoid_subset (W : Mat ℝ m n) (b : Vec ℝ m)
    (X : PolyZonotope (Vec ℝ n)) {ε : ℝ} (hε : 0 < ε) : ∃ sch : Schedule,
      construct ((sigmoidLinearSigmoidNetwork W b).propagateAt sch X)
        ⊆ (sigmoidLinearSigmoidNetwork W b).outputSet X + Metric.closedBall 0 ε :=
  (sigmoidLinearSigmoidNetwork W b).exists_schedule_propagateAt_subset
    (sigmoidLinearSigmoidNetwork_convergent W b) X ε hε

end CORALean.Real
