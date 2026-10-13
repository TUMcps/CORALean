import CORALean.ContSet.PolyZonotope.Float.Instances
import CORALean.ContSet.PolyZonotope.Float.Operations.Plus
import CORALean.NN.Graph.Operations.FloatBiasPoint
import CORALean.NN.Graph.Operations.FloatRightMat

/-!
# CORA's `nnGNNLinearLayer` on a float polynomial zonotope

`H ↦ H Wᵀ + 1 bᵀ` on the stacked node features (`GNN.flatten`): `PolyZonotope.mtimes` at the
matrix of `H ↦ H Wᵀ`, then `PolyZonotope.plus` with the bias point. The rounding goes into the
error box.
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
def GNN.linear (W : Mat 𝕋 F₂ F₁) (b : Vec 𝕋 F₂) (pZ : PolyZonotope (Vec 𝕋 (N * F₁))) :
    PolyZonotope (Vec 𝕋 (N * F₂)) :=
  PolyZonotope.plus (PolyZonotope.mtimes (GNN.rightMat N W.transpose) pZ) (GNN.biasPoint N b)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
