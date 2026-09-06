import CORALean.NN.Layers.Linear
import CORALean.NN.Layers.SigmoidPolyRefine

/-!
# A network with more than one layer in it

Sigmoid, then `W x + b`, then sigmoid: the smallest chain in which every part of
the refinement loop [1] is doing work. Two layers spend levels and one does not,
the dimension changes in the middle, and the first activation's residual has to
survive both layers after it — which is the case a single-layer network says
nothing about.

The weights are arbitrary, so this is a family and not an example: nothing below
depends on what `W` and `b` are, only on the shape.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n m : ℕ}

/-- Two refinable activations around a linear layer, which has nothing to spend
and so takes every level as itself. -/
noncomputable def sigmoidLinearSigmoidNetwork (W : Mat ℝ m n) (b : Vec ℝ m) :
    RefinableNetwork 𝒫𝒵 n m :=
  .cons (Layer.activationPolyRefinable sigmoidPolyFamily)
    (.cons (Layer.linear W b).refinable
      (.cons (Layer.activationPolyRefinable sigmoidPolyFamily) .nil))

end CORALean.Real
