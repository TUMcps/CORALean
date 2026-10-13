module

public import CORALean.NN.Graph.Operations.ReduceGNNForNode
public import CORALean.NN.Graph.Theorems.BallSubsetReduceKeep
public import CORALean.NN.Graph.Theorems.ReducedStepsRow

@[expose] public section

/-!
# The reduced network answers for node `v` exactly
`reduceGNNForNode`'s result at `v` equals row `v` of the `L` message-passing steps on the whole
graph: an equality, not an enclosure, since a dropped node is one the receptive field of `v`
never reads [1, §4.3].

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every row of the reduced network that names `v` is row `v` of the unreduced chain. -/
theorem GNN.reduceGNNForNode_exact {N F : ℕ} (A : Mat ℝ N N) (v : Fin N) (L : ℕ)
    (W : ℕ → Mat ℝ F F) (X : Mat ℝ N F) (a : ↥(GNN.reduceKeep A v L L))
    (ha : (a : Fin N) = v) :
    GNN.reduceGNNForNode A v L W X a
      = GNN.evalSteps (GNN.messagePassing A) L (fun i : Fin L => W i) X v :=
  GNN.reducedSteps_row A v L (GNN.reduceKeep A v L)
    (fun k hk => GNN.ball_subset_reduceKeep A v L k hk) W X _ (fun _ _ => rfl) a ha

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
