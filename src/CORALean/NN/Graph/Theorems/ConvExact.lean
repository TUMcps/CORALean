module

public import CORALean.ContSet.PolyZonotope.Real.Theorems.MapExact
public import CORALean.NN.Graph.Operations.Gcn
public import CORALean.NN.Graph.Theorems.GcnLinApply

@[expose] public section

/-!
# A graph convolutional layer loses nothing, at any matrix `P`

`PolyZonotope.map_exact` at `H ↦ P H W`, and that is the entire proof: a linear
map of the ambient space cannot touch the monomials, and `map_exact` never
reads the shape of that space — so the matrix case is the theorem already in
the tree, instantiated.

`gcn_exact` assumes nothing about `P`, which is what makes it survive an
uncertain graph. The corollary at `P = messagePassing A`, [1, Prop. 2] itself,
is `ConvExactOfAdjacency.lean`.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N F₁ F₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem GNN.gcn_exact (P : Mat ℝ N N) (W : Mat ℝ F₁ F₂) (pZ : PolyZonotope (Mat ℝ N F₁)) :
    (fun H => P * H * W) '' pZ.construct = (GNN.gcn P W pZ).construct := by -- --- PROOF ---
  -- the image is taken at the linear map, which is what `gcnLin_apply` says
  have h : (fun H : Mat ℝ N F₁ => P * H * W) = GNN.gcnLin P W :=
    funext fun H => (GNN.gcnLin_apply P W H).symm
  rw [h]
  exact PolyZonotope.map_exact (GNN.gcnLin P W) pZ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
