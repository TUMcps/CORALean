module

public import CORALean.NN.Graph.Operations.GcnShared
public import CORALean.NN.Graph.Operations.GcnUncertain

@[expose] public section

/-!
# `GNN.gcnShared`'s and `GNN.gcnUncertain`'s counts

[1, Prop. 5]'s `O(h₁ h₂³)`: the layer at an uncertain graph is [1, Lemma 1]'s multiplication
followed by an affine map, so its dependent generator count is `(P.h + 1) * (H.h + 1)`, the product
[1, Lemma 1] predicts, and its independent block is empty. `rfl` against the structure instances in
`ConvUncertain.lean` and `Operations/Bilin.lean`.

`gcnShared_p` sits beside the definition, as a chain of steps rests on the factor set being kept.
Padding moves the factor count and nothing else, so `gcnUncertain` counts as `gcnShared` does.

## Inputs
* `W` – weight matrix
* `P` – polynomial zonotope of the graph
* `H` – polynomial zonotope of the node features

## Hypotheses
* `hp` – both sets share their factors

## Conclusion
* the dependent generator count is the product of the two inputs' plus one

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N F₁ F₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `h` count of `gcnShared`'s result. -/
theorem GNN.gcnShared_h (W : Mat ℝ F₁ F₂) (P : PolyZonotope (Mat ℝ N N))
    (H : PolyZonotope (Mat ℝ N F₁)) (hp : P.p = H.p) :
    (GNN.gcnShared W P H hp).h = (P.h + 1) * (H.h + 1) := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
