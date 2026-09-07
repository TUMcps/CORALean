import CORALean.NN.Graph.Theorems.ConvExact

/-!
# `[1, Prop. 2]` itself: the layer at the graph's own message passing

Split out of `ConvExact.lean` (issue #62): `gcn_exact` is the general fact,
true of any `P`; this is the corollary at `P = messagePassing A`, which is the
proposition as `[1]` actually states it.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {N F₁ F₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 2] itself: the layer at the graph's own message passing. -/
theorem GNN.gcn_exact_of_adjacency (A : Mat ℝ N N) (W : Mat ℝ F₁ F₂)
    (pZ : PolyZonotope (Mat ℝ N F₁)) :
    (fun H => GNN.messagePassing A * H * W) '' pZ.construct
      = (GNN.gcn (GNN.messagePassing A) W pZ).construct :=
  GNN.gcn_exact _ W pZ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
