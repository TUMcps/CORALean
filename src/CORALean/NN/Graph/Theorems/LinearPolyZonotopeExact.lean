module

public import CORALean.ContSet.PolyZonotope.Real.Theorems.MapExact
public import CORALean.ContSet.PolyZonotope.Real.Theorems.ShiftExact
public import CORALean.NN.Graph.Operations.LinearPolyZonotope

@[expose] public section

/-!
# The graph linear layer on a polynomial zonotope is exact

An equality: the layer is an affine map of the node features, `map` is exact at its linear part
and `shift` at its bias, so nothing is given away.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N F₁ F₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem GNN.linearPolyZonotope_exact (W : Mat ℝ F₂ F₁) (b : Vec ℝ F₂)
    (pZ : PolyZonotope (Mat ℝ N F₁)) :
    GNN.linear W b '' pZ.construct = (GNN.linearPolyZonotope W b pZ).construct := by
  rw [GNN.linearPolyZonotope, ← PolyZonotope.shift_exact, ← PolyZonotope.map_exact,
    ← Set.image_comp]
  rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
