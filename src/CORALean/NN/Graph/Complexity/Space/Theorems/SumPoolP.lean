module

public import CORALean.NN.Graph.Operations.SumPool

@[expose] public section

/-!
# `GNN.sumPool`'s counts

[1, Thm. 1]'s "the global pooling layer does not change the number of
generators", read off the construction: summing across nodes is one
`PolyZonotope.map`, so all three counts stand and only the ambient type moves
from `Mat ℝ N F` to `Vec ℝ F`. `rfl` against the structure instance in
`Operations/Map.lean`.

That the shape changes and the counts do not is what lets the layers after the
pooling be the ordinary vector-shaped ones with nothing paid in between.

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

variable {N F : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `p` count of `sumPool`'s result. -/
theorem GNN.sumPool_p (pZ : PolyZonotope (Mat ℝ N F)) : (GNN.sumPool pZ).p = pZ.p := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
