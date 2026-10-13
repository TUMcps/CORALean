module

public import CORALean.NN.Definitions.Chain
public import CORALean.NN.Operations.LayerSensitivity

@[expose] public section

/-!
# The sensitivity of a network

CORA's `calcSensitivity`: a forward pass to place each layer's input, then the
Jacobians multiplied back from the output, `S ← S · Jᵢ` — the chain rule and
nothing else [1, Def. 2.3].

Written as the recursion the graph already is: the rest of the network's
sensitivity at this layer's output, times this layer's own. Every partial
product is one of CORA's `layers{i}.sensitivity`, and that is the quantity the
refinement heuristic reads — how far a neuron of layer `i` moves the output, so
what its approximation error costs there.

Total wherever `layerSensitivity` is, so a ReLU network has one. Whether it is
the derivative is `Theorems.SensitivityFDeriv`'s business and nobody else's.

Over a `Chain` and not a `NeuralNetwork`: `Layer` stores no map, and a `Prop`
cannot be recursed through, so the layer maps have to arrive as data.

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

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Chain.sensitivity : ∀ {n m : ℕ}, Chain n m → Vec ℝ n → Mat ℝ m n
  | _, _, .nil, _ => 1
  | _, _, .cons f rest, x => rest.sensitivity (f x) * layerSensitivity f x

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
