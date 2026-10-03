import CORALean.ContSet.PolyZonotope.Real.Operations.Map
import CORALean.ContSet.PolyZonotope.Real.Operations.Shift
import CORALean.NN.Graph.Operations.Linear

/-!
# CORA's `nnGNNLinearLayer` on a matrix polynomial zonotope

`evaluatePolyZonotope`: the affine map with bias on the centre `c`, and without the bias on both
generator blocks `G` and `GI`. That is `PolyZonotope.map` at the linear part, then `shift` by the
bias: the layer induces no outer approximation.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N F₁ F₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `c = aux_affineMap(c, true)`, `G = aux_affineMap(G, false)`, `GI = aux_affineMap(GI, false)`. -/
def GNN.linearPolyZonotope (W : Mat ℝ F₂ F₁) (b : Vec ℝ F₂) (pZ : PolyZonotope (Mat ℝ N F₁)) :
    PolyZonotope (Mat ℝ N F₂) :=
  (pZ.map (GNN.linearLin W)).shift (GNN.linearBias N b)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
