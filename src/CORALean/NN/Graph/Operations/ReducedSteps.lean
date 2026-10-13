import CORALean.NN.Graph.Operations.MessagePassing

/-!
# Message passing on a shrinking node set, `reduceGNNForNode`'s network
CORA's reduced network [1, §4.3] runs a `nnGCNLayer` on the kept nodes and then a
`nnGNNProjectionLayer` that keeps fewer of them, whose `updateMessagePassing` restricts the
stored `D̃^(-1/2) Ã D̃^(-1/2)` of the *whole* graph to the kept rows and columns. As the kept
sets are nested, a step and its projection are one product with `P` restricted to the new rows
and the old columns. `S k` is the node set before step `k`; the features start on `S 0`.

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

variable {N F : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `L` steps of `Y ↦ P[S (k+1), S k] Y W k`, the features living on `S k` before step `k`. -/
def GNN.reducedSteps (P : Mat ℝ N N) :
    (L : ℕ) → (S : ℕ → Finset (Fin N)) → (W : ℕ → Mat ℝ F F) →
      Matrix ↥(S 0) (Fin F) ℝ → Matrix ↥(S L) (Fin F) ℝ
  | 0, _, _, Y => Y
  | L + 1, S, W, Y =>
    GNN.reducedSteps P L (fun k => S (k + 1)) (fun k => W (k + 1))
      (P.submatrix (fun a : ↥(S 1) => (a : Fin N)) (fun b : ↥(S 0) => (b : Fin N)) * Y * W 0)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
