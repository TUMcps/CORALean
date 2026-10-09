import CORALean.NN.Graph.Operations.Ball

/-!
# The node sets `reduceGNNForNode` keeps
CORA's `reduceGNNForNode` [1, §4.3] keeps, before message-passing step `k` (`k = 0` the input), the
nodes at distance at most `L - k + 1` from the node of interest `n0`, the extra hop being its
normalisation margin; after the last step it keeps `n0` alone. `ball A v r` is that distance
neighbourhood. CORA's code returns early for no step only in a comment, so at `L = 0` the
nodes within distance `1` are kept (see [FINDINGS](../../../../../FINDINGS.md)).

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The nodes kept before step `k` of `L`: the ball of radius `L - k + 1`, and `{v}` after the
last step (for `L ≥ 1`, as CORA's code). -/
noncomputable def GNN.reduceKeep (A : Mat ℝ N N) (v : Fin N) (L k : ℕ) : Finset (Fin N) :=
  if 0 < L ∧ k = L then {v} else GNN.ball A v (L - k + 1)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
