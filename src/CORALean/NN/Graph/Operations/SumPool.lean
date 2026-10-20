module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Map
public import CORALean.NN.Graph.Operations.SumPoolLin

@[expose] public section

/-!
# Summation pooling on a matrix polynomial zonotope

CORA's `nnGNNGlobalPoolingLayer` at the sum, [1, Prop. 3]: linear, so its
propagation is `PolyZonotope.map` at `sumPoolLin` and its guarantee
`map_exact`.

## Inputs
* `pZ` – node features as a polynomial zonotope

## Output
* polynomial zonotope of the features summed over the nodes

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Claude Sonnet 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N F : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Summation pooling on a matrix polynomial zonotope, landing in the vector
shape the layers after it read. -/
def GNN.sumPool (pZ : PolyZonotope (Mat ℝ N F)) : PolyZonotope (Vec ℝ F) :=
  pZ.map (GNN.sumPoolLin N F)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
