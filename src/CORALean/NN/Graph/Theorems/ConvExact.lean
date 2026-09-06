import CORALean.ContSet.PolyZonotope.Real.Theorems.MapExact
import CORALean.NN.Graph.Conv

/-!
# A graph convolutional layer loses nothing

[1, Prop. 2]. `PolyZonotope.map_exact` at `H ↦ P H W`, and that is the entire
proof: a linear map of the ambient space cannot touch the monomials, and
`map_exact` never reads the shape of that space — so the matrix case is the
theorem already in the tree, instantiated.

`gcn_exact` assumes nothing about `P`, which is what makes it survive an
uncertain graph: only the corollary names `messagePassing`, and it is that
corollary which is the proposition as [1] states it.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {N F₁ F₂ : ℕ}

theorem GNN.gcn_exact (P : Mat ℝ N N) (W : Mat ℝ F₁ F₂) (PZ : PolyZonotope (Mat ℝ N F₁)) :
    (fun H => P * H * W) '' PZ.construct = (GNN.gcn P W PZ).construct := by
  -- the image is taken at the linear map, which is what `gcnLin_apply` says
  have h : (fun H : Mat ℝ N F₁ => P * H * W) = GNN.gcnLin P W :=
    funext fun H => (GNN.gcnLin_apply P W H).symm
  rw [h]
  exact PolyZonotope.map_exact (GNN.gcnLin P W) PZ

/-- [1, Prop. 2] itself: the layer at the graph's own message passing. -/
theorem GNN.gcn_exact_of_adjacency (A : Mat ℝ N N) (W : Mat ℝ F₁ F₂)
    (PZ : PolyZonotope (Mat ℝ N F₁)) :
    (fun H => GNN.messagePassing A * H * W) '' PZ.construct
      = (GNN.gcn (GNN.messagePassing A) W PZ).construct :=
  GNN.gcn_exact _ W PZ

end CORALean.Real
