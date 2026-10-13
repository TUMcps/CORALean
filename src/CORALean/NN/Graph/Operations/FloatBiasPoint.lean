module

public import CORALean.ContSet.PolyZonotope.Float.Operations.Origin
public import CORALean.NN.Graph.Operations.Flatten

@[expose] public section

/-!
# The bias `1 bᵀ` as a point

The bias row repeated at every node, stacked (`GNN.flatten`), as a polynomial zonotope with no
generators: the origin with its centre replaced by it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {F : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The point `1 bᵀ` (the same bias at each of `N` nodes), stacked. -/
def GNN.biasPoint (N : ℕ) (b : Vec 𝕋 F) : PolyZonotope (Vec 𝕋 (N * F)) :=
  { PolyZonotope.origin (N * F) with c := fun r => b (finProdFinEquiv.symm r).2 }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
