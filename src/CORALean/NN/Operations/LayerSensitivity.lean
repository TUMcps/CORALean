import CORALean.NN.Layer

/-!
# A layer's sensitivity

CORA's `evaluateSensitivity`: the Jacobian of what the layer computes at a
point — rows output neurons, columns input neurons — which is what weights a
neuron's approximation error by how much it moves the output [1].

Total, and carrying no obligation, because a `Layer` supplies `eval` and an
enclosure and can supply nothing about derivatives: ReLU has none at zero, so a
derivative field would be a lie and a differentiability hypothesis would exclude
the commonest activation. Sensitivity is a *ranking*, and every refinement it
orders is sound — as `reduceBy_outer`'s metric and `Relaxation.ofDeriv`'s slope
are — so it is `fderiv` of `eval` with no side condition, junk-valued exactly
where `eval` has none. `Theorems.SensitivityFDeriv` is what makes it a good
heuristic rather than an arbitrary one.

A matrix and not the continuous linear map it comes from: the matrix product is
what composes the chain, and the columns are what the heuristic reads.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}

noncomputable def Layer.sensitivity (L : Layer S n m) (x : Vec ℝ n) : Mat ℝ m n :=
  LinearMap.toMatrix' (fderiv ℝ L.eval x : Vec ℝ n →L[ℝ] Vec ℝ m).toLinearMap

end CORALean.Real
