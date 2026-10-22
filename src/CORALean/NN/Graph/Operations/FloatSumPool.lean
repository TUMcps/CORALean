module

public import CORALean.ContSet.PolyZonotope.Float.Instances
public import CORALean.NN.Graph.Operations.Flatten
public import CORALean.Global.Float.FloatOps

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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
open FloatOps
variable {𝕋 : Type} [FloatOps 𝕋]

/-- The matrix of `H ↦ 1 H` on the stacked `N × F` node features. -/
def GNN.aux_sumPoolMat (N F : ℕ) : Mat 𝕋 F (N * F) :=
  fun j c => if (finProdFinEquiv.symm c).2 = j then one else zero

end


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Each feature summed across the nodes of the stacked node features. -/
def GNN.sumPool (pZ : PolyZonotope (Vec 𝕋 (N * F))) : PolyZonotope (Vec 𝕋 F) :=
  PolyZonotope.mtimes (GNN.aux_sumPoolMat N F) pZ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
