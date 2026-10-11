import CORALean.NN.Graph.Operations.EvalStepsLayers
import CORALean.NN.Graph.Theorems.SubmatrixMulOfClosed

/-!
# A closed subgraph computes the same layered chain

`[1, Sec. 4.3]`: `L` message-passing steps with a per-node layer after each, run on the whole
graph and restricted to a closed subgraph, are the same matrix as the steps run on the subgraph
alone. A layer reads a row and nothing else, so restricting commutes with it.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- `L` layered steps on the whole graph, restricted to a closed subgraph, equal the steps on the
subgraph alone. -/
theorem GNN.evalStepsLayers_submatrix {N K F : ℕ} (Pm : Mat ℝ N N) (κ : Fin K → Fin N)
    (hinj : Function.Injective κ) (hclosed : ∀ k i, (∀ l, κ l ≠ i) → Pm (κ k) i = 0)
    (L : ℕ) (g : Fin L → Vec ℝ F → Vec ℝ F) (X : Mat ℝ N F) :
    (GNN.evalStepsLayers Pm L g X).submatrix κ id
      = GNN.evalStepsLayers (Pm.submatrix κ κ) L g (X.submatrix κ id) := by -- --- PROOF ---
  induction L generalizing X with
  | zero => rfl
  | succ L ih =>
      -- the product restricts by closure, and the layer acts row by row
      have hstep : (Matrix.of fun u => g 0 ((Pm * X) u)).submatrix κ id
          = Matrix.of fun k => g 0 ((Pm.submatrix κ κ * X.submatrix κ id) k) := by
        funext k
        have h := congrFun (GNN.submatrix_mul_of_closed Pm X κ hinj hclosed) k
        show g 0 ((Pm * X) (κ k)) = g 0 ((Pm.submatrix κ κ * X.submatrix κ id) k)
        rw [← h]
        rfl
      show (GNN.evalStepsLayers Pm L (fun i => g i.succ)
          (Matrix.of fun u => g 0 ((Pm * X) u))).submatrix κ id
        = GNN.evalStepsLayers (Pm.submatrix κ κ) L (fun i => g i.succ)
            (Matrix.of fun k => g 0 ((Pm.submatrix κ κ * X.submatrix κ id) k))
      rw [← hstep, ih (fun i => g i.succ)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
