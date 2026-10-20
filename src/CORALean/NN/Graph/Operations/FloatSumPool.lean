module

public import CORALean.ContSet.PolyZonotope.Float.Instances
public import CORALean.NN.Graph.Operations.FloatSumPoolMat

@[expose] public section

/-!
# Summation pooling on a float polynomial zonotope

CORA's `nnGNNGlobalPoolingLayer` at the sum: `PolyZonotope.mtimes` at the pooling matrix, landing
in `Vec 𝕋 F`, the shape every layer after it reads.

## Inputs
* `pZ` – stacked node features

## Output
* polynomial zonotope of the features summed over the nodes
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {N F : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Each feature summed across the nodes of the stacked node features. -/
def GNN.sumPool (pZ : PolyZonotope (Vec 𝕋 (N * F))) : PolyZonotope (Vec 𝕋 F) :=
  PolyZonotope.mtimes (GNN.sumPoolMat N F) pZ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
