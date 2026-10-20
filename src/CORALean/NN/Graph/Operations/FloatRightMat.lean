module

public import CORALean.NN.Graph.Operations.Flatten
public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# `W` applied to every node row, as one float matrix

On the stacked node-feature vector (`GNN.flatten`), `H ↦ H W` is the matrix with entry `W j j'`
where the two positions share a node and `0` elsewhere. It stores the entries of `W` and the
exact zero only, so nothing rounds in building it.

## Inputs
* `N` – number of nodes
* `W` – weight matrix

## Output
* matrix applying the weights to every node row
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {F₁ F₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The matrix of `H ↦ H W` on the stacked `N × F₁` node features. -/
def GNN.rightMat (N : ℕ) (W : Mat 𝕋 F₁ F₂) : Mat 𝕋 (N * F₂) (N * F₁) :=
  fun r c => if (finProdFinEquiv.symm r).1 = (finProdFinEquiv.symm c).1
    then W (finProdFinEquiv.symm c).2 (finProdFinEquiv.symm r).2 else zero

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
