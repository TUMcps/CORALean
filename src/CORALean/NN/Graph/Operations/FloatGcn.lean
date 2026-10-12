import CORALean.ContSet.PolyZonotope.Float.Instances
import CORALean.NN.Graph.Operations.FloatLeftMat
import CORALean.NN.Graph.Operations.FloatRightMat

/-!
# The graph convolutional layer on a float polynomial zonotope

CORA's `nnGCNLayer`, `H ↦ P H W`, on the stacked node features (`GNN.flatten`): `W` then `P`,
each as one `PolyZonotope.mtimes` at a matrix holding only entries of `P`, `W` and the exact zero.
The rounding of the two products goes into the error box.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {N F₁ F₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The layer on the stacked node features, an outer approximation of the exact one. -/
def GNN.gcn (P : Mat 𝕋 N N) (W : Mat 𝕋 F₁ F₂) (pZ : PolyZonotope 𝕋 (N * F₁)) :
    PolyZonotope 𝕋 (N * F₂) :=
  PolyZonotope.mtimes (GNN.leftMat P F₂) (PolyZonotope.mtimes (GNN.rightMat N W) pZ)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
