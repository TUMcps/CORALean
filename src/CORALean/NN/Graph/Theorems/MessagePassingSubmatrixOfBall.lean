module

public import CORALean.NN.Graph.Operations.MessagePassing
public import CORALean.NN.Graph.Theorems.DegreeSubmatrixOfBall

@[expose] public section

/-!
# `[1, §4.3]`'s extra hop, for `messagePassing` itself

Both endpoints' degrees are what `P = D̃^(-1/2) Ã D̃^(-1/2)` reads, so this is
`degree_submatrix_of_ball` applied twice plus the numerator, `(A + 1) i j`, which the
submatrix reads off directly. Mind the `+ 1`: its off-diagonal entries are zero, and its
diagonal survives reindexing only because `κ` is injective — the same fact
`degree_submatrix_of_ball` already proves for a column, reused here for a single entry.

Radius `r`, not `r + 1`, at `i` and `j` themselves: it is only *computing* each degree that
needs the extra ring, exactly as `degree_submatrix_of_ball`'s docstring explains.

## Inputs
* `N` – number of nodes
* `A` – adjacency matrix
* `v` – center node
* `r` – radius in hops
* `K` – number of kept nodes
* `κ` – indices of the kept nodes
* `i` – first node
* `j` – second node
* `ki` – index of the first node among the kept ones
* `kj` – index of the second node among the kept ones

## Hypotheses
* `hA` – adjacency entries are nonnegative
* `hSymm` – adjacency matrix is symmetric
* `hinj` – kept indices are distinct
* `hκ` – kept nodes contain the ball one hop larger
* `hi` – first node lies in the ball of radius r
* `hj` – second node lies in the ball of radius r
* `hki` – index names the first node
* `hkj` – index names the second node

## Conclusion
* the message on the subgraph equals the message in the whole graph

## References

* [1] [T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph Convolutional Networks
      with Uncertain Node Features and Uncertain Graph Structure". Transactions on Machine Learning
      Research, 2025.](../../../../../references/2025/ladner-tmlr-gcn.md)
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   07-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- Message passing computed on the subgraph a ball's `κ` enumerates agrees with the whole
graph's, between any two nodes whose own balls reach only one radius short. -/
theorem GNN.messagePassing_submatrix_of_ball {N : ℕ} (A : Mat ℝ N N) (hA : ∀ i j, 0 ≤ A i j)
    (hSymm : ∀ i j, A i j = A j i) (v : Fin N) (r : ℕ) {K : ℕ} (κ : Fin K → Fin N)
    (hinj : Function.Injective κ) (hκ : GNN.ball A v (r + 1) ⊆ Finset.univ.image κ)
    {i j : Fin N} (hi : i ∈ GNN.ball A v r) (hj : j ∈ GNN.ball A v r)
    (ki kj : Fin K) (hki : κ ki = i) (hkj : κ kj = j) : -- --- CONCL ---
    GNN.messagePassing (A.submatrix κ κ) ki kj = GNN.messagePassing A i j := by -- --- PROOF ---
  have hdi : GNN.degree (A.submatrix κ κ) ki = GNN.degree A i :=
    GNN.degree_submatrix_of_ball A hA hSymm v r κ hinj hκ hi ki hki
  have hdj : GNN.degree (A.submatrix κ κ) kj = GNN.degree A j :=
    GNN.degree_submatrix_of_ball A hA hSymm v r κ hinj hκ hj kj hkj
  -- the numerator reads the same entry of `A + 1`, `κ` reading it exactly like a submatrix
  have hnum : (A.submatrix κ κ + 1) ki kj = (A + 1) (κ ki) (κ kj) := by
    by_cases h : ki = kj
    · simp [h, Matrix.add_apply, Matrix.submatrix_apply]
    · simp [Matrix.add_apply, Matrix.submatrix_apply, Matrix.one_apply_ne h,
        Matrix.one_apply_ne (fun hc => h (hinj hc))]
  rw [hki, hkj] at hnum
  show (A.submatrix κ κ + 1) ki kj / (Real.sqrt (GNN.degree (A.submatrix κ κ) ki) *
      Real.sqrt (GNN.degree (A.submatrix κ κ) kj))
      = (A + 1) i j / (Real.sqrt (GNN.degree A i) * Real.sqrt (GNN.degree A j))
  rw [hnum, hdi, hdj]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
