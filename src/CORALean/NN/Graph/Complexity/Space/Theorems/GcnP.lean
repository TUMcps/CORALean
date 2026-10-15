module

public import CORALean.NN.Graph.Operations.Gcn

@[expose] public section

/-!
# `GNN.gcn`'s counts

The layer at a known graph is one `PolyZonotope.map`, so none of the three
counts move — [1, Thm. 1]'s "linear layers do not change the number of
generators", read off the construction that computes such a layer. `rfl`
against the structure instance in `Operations/Map.lean`.

This is the layer [1, Prop. 2] calls exact; the counts say the other half of
that, which is that exactness is not bought with generators.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N F₁ F₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `p` count of `gcn`'s result. -/
theorem GNN.gcn_p (P : Mat ℝ N N) (W : Mat ℝ F₁ F₂) (pZ : PolyZonotope (Mat ℝ N F₁)) :
    (GNN.gcn P W pZ).p = pZ.p := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
