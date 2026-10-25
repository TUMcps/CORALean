module

public import CORALean.NN.Graph.Operations.EvalSteps
public import CORALean.NN.Graph.Theorems.SubmatrixMulOfClosed

@[expose] public section

/-!
# A closed subgraph computes the same chain, not an enclosure of it

`[1, §4.3]`'s payoff over `submatrix_mul_of_closed`: running `L` message-passing steps on the whole
graph and then restricting to the subgraph gives *the same matrix* as restricting first. An
equality, not an outer approximation, because at every step `hclosed` says the rest of the graph
contributes nothing.

`aux_submatrix_mul_right` is the other half a step needs: multiplying by a weight `W` on the right
never mixes rows, so restricting rows commutes with it for free.

## Inputs
* `N` – number of nodes
* `K` – number of kept nodes
* `F` – feature width
* `Pm` – message-passing matrix
* `κ` – indices of the kept nodes
* `L` – number of steps
* `W` – weights of the steps
* `X` – node-feature matrix

## Hypotheses
* `hinj` – kept indices are distinct
* `hclosed` – the kept nodes receive nothing from outside

## Conclusion
* the chain on the whole graph restricted to the subgraph equals the chain on the subgraph

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph Convolutional Networks
      with Uncertain Node Features and Uncertain Graph Structure". Transactions on Machine Learning
      Research, 2025.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A right multiplication never touches rows, so restricting them commutes past it. -/
theorem GNN.aux_submatrix_mul_right {N K F : ℕ} (A : Mat ℝ N F) (κ : Fin K → Fin N)
    (W : Mat ℝ F F) : (A * W).submatrix κ id = A.submatrix κ id * W := by
  funext i j
  simp [Matrix.mul_apply]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `L` steps on the whole graph, restricted to a closed subgraph, equal `L` steps run on
the subgraph alone: locality holds over the whole chain, not just one step of it. -/
theorem GNN.evalSteps_submatrix {N K F : ℕ} (Pm : Mat ℝ N N) (κ : Fin K → Fin N)
    (hinj : Function.Injective κ) (hclosed : ∀ k i, (∀ l, κ l ≠ i) → Pm (κ k) i = 0)
    (L : ℕ) (W : Fin L → Mat ℝ F F) (X : Mat ℝ N F) : -- --- CONCL ---
    (GNN.evalSteps Pm L W X).submatrix κ id
      = GNN.evalSteps (Pm.submatrix κ κ) L W (X.submatrix κ id) := by -- --- PROOF ---
  induction L generalizing X with
  | zero => rfl
  | succ L ih =>
      -- one step matches through `submatrix_mul_of_closed`; the rest is `ih`'s shorter chain
      have hstep : (Pm * X * W 0).submatrix κ id
          = Pm.submatrix κ κ * X.submatrix κ id * W 0 := by
        rw [GNN.aux_submatrix_mul_right, GNN.submatrix_mul_of_closed Pm X κ hinj hclosed]
      show (GNN.evalSteps Pm L (fun i => W i.succ) (Pm * X * W 0)).submatrix κ id
        = GNN.evalSteps (Pm.submatrix κ κ) L (fun i => W i.succ)
            (Pm.submatrix κ κ * X.submatrix κ id * W 0)
      rw [← hstep, ih (fun i => W i.succ) (Pm * X * W 0)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
