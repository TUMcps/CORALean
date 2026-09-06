import CORALean.NN.NeuralNetwork
import CORALean.NN.Operations.LayerSensitivity

/-!
# The sensitivity of a network

CORA's `calcSensitivity`: a forward pass to place each layer's input, then the
Jacobians multiplied back from the output, `S ← S · Jᵢ` — the chain rule and
nothing else [1].

Written as the recursion the graph already is: the rest of the network's
sensitivity at this layer's output, times this layer's own. Every partial
product is one of CORA's `layers{i}.sensitivity`, and that is the quantity the
refinement heuristic reads — how far a neuron of layer `i` moves the output, so
what its approximation error costs there.

Total wherever `Layer.sensitivity` is, so a ReLU network has one. Whether it is
the derivative is `Theorems.SensitivityFDeriv`'s business and nobody else's.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def NeuralNetwork.sensitivity :
    ∀ {n m : ℕ}, NeuralNetwork S n m → Vec ℝ n → Mat ℝ m n
  | _, _, .nil, _ => 1
  | _, _, .cons L rest, x => rest.sensitivity (L.eval x) * L.sensitivity x

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
