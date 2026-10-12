import CORALean.ContSet.PolyZonotope.Float.Instances
import CORALean.NN.Graph.Operations.FloatSumPoolMat

/-!
# Summation pooling on a float polynomial zonotope

CORA's `nnGNNGlobalPoolingLayer` at the sum: `PolyZonotope.mtimes` at the pooling matrix, landing
in `Vec 𝕋 F`, the shape every layer after it reads.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {N F : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Each feature summed across the nodes of the stacked node features. -/
def GNN.sumPool (pZ : PolyZonotope 𝕋 (N * F)) : PolyZonotope 𝕋 F :=
  PolyZonotope.mtimes (GNN.sumPoolMat N F) pZ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
