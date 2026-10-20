module

public import CORALean.NN.Graph.Operations.Flatten
public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# `P` applied to every feature column, as one float matrix

On the stacked node-feature vector (`GNN.flatten`), `H ↦ P H` is the matrix with entry `P i i'`
where the two positions share a feature and `0` elsewhere. It stores the entries of `P` and the
exact zero only, so nothing rounds in building it; the rounding is paid by `PolyZonotope.mtimes`.

## Inputs
* `P` – message-passing matrix
* `F` – feature width

## Output
* matrix applying the message passing to every feature column
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The matrix of `H ↦ P H` on the stacked `N × F` node features. -/
def GNN.leftMat (P : Mat 𝕋 N N) (F : ℕ) : Mat 𝕋 (N * F) (N * F) :=
  fun r c => if (finProdFinEquiv.symm r).2 = (finProdFinEquiv.symm c).2
    then P (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm c).1 else zero

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
