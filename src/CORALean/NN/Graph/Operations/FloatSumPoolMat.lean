module

public import CORALean.NN.Graph.Operations.Flatten
public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# Summation pooling as a float matrix

On the stacked node-feature vector (`GNN.flatten`), the sum of each feature across the nodes is the
matrix with entry `1` where the position carries that feature and `0` elsewhere: only the exact
`1` and `0`, so nothing rounds in building it.

## Inputs
* `N` – number of nodes
* `F` – feature width

## Output
* matrix summing every feature over the nodes
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The matrix of `H ↦ 1 H` on the stacked `N × F` node features. -/
def GNN.sumPoolMat (N F : ℕ) : Mat 𝕋 F (N * F) :=
  fun j c => if (finProdFinEquiv.symm c).2 = j then one else zero

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
