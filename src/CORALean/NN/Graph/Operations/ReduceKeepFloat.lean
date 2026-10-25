module

public import CORALean.NN.Graph.Operations.BallFloat

@[expose] public section

/-!
# The node sets `reduceGNNForNode` keeps, on an edge test
`GNN.reduceKeep` with `GNN.ballFloat`: before message-passing step `k` of `L`, the nodes within
distance `L - k + 1` of `v`, and `{v}` alone after the last step (for `L ≥ 1`) [1, §4.3].

## Inputs
* `E` – Boolean edge test
* `v` – node of interest
* `L` – number of message-passing steps
* `k` – step index

## Output
* nodes kept before step k

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph Convolutional Networks
      with Uncertain Node Features and Uncertain Graph Structure". Transactions on Machine Learning
      Research, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def GNN.reduceKeepFloat (E : Fin N → Fin N → Bool) (v : Fin N) (L k : ℕ) : Finset (Fin N) :=
  if 0 < L ∧ k = L then {v} else GNN.ballFloat E v (L - k + 1)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
