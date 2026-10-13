module

public import CORALean.NN.Layers.Layer
public import Mathlib.Analysis.Calculus.FDeriv.Defs

@[expose] public section

/-!
# A layer's sensitivity

CORA's `evaluateSensitivity`: the Jacobian of what the layer computes at a
point — rows output neurons, columns input neurons — which is what weights a
neuron's approximation error by how much it moves the output [1, Def. 2.3].

Total, and carrying no obligation: ReLU has no derivative at zero, so asking for
one would be a lie and a differentiability hypothesis would exclude the
commonest activation. Sensitivity is a *ranking*, and every refinement it orders
is sound, so it is `fderiv` of the map with no side condition, junk-valued
exactly where that map has none. `Theorems.SensitivityFDeriv` is what makes it a
good heuristic rather than an arbitrary one.

A function and not a `Layer`, since `Layer` stores none: `Chain` is where the
layer maps live. A matrix and not the continuous linear map it comes from: the
matrix product is what composes the chain.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def layerSensitivity (f : Vec ℝ n → Vec ℝ m) (x : Vec ℝ n) : Mat ℝ m n :=
  LinearMap.toMatrix' (fderiv ℝ f x : Vec ℝ n →L[ℝ] Vec ℝ m).toLinearMap

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
