import CORALean.NN.Layers.Linear
import CORALean.NN.Layers.SigmoidPolyRefine

/-!
# The two-layer network `σ(W x + b)`

The network [1, Prop. 4.13] is stated on: one linear layer, one activation, and
nothing after it. The linear layer spends no level and the activation spends all
of them, so this is the smallest chain in which refinement has anything to do
and the only one in which no residual has to travel anywhere.

`SigmoidLinearSigmoid` is the next case up, and the difference is the point: a
residual left here reaches the output untouched, while there it passes through a
matrix and a second activation first.

The weights are arbitrary, so this is a family and not an example.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       12-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A linear layer, which takes every level as itself, and the one refinable
activation behind it. -/
noncomputable def linearSigmoidNetwork (W : Mat ℝ m n) (b : Vec ℝ m) :
    RefinableNetwork 𝒫𝒵 n m :=
  .cons ((Layer.linear W b).refinable (Layer.linear_sound W b))
    (.cons (Layer.activationPolyRefinable sigmoidPolyFamily) .nil)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
