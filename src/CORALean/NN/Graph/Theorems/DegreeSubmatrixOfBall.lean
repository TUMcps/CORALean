module

public import CORALean.NN.Graph.Operations.Degree
public import CORALean.NN.Graph.Theorems.BallSubsetSucc

@[expose] public section

/-!
# A degree is decided by one ring beyond the ball

`[1, §4.3]`'s extra hop, stated for `degree` itself: `GNN.degree A j` sums a whole column of `Ã = A
+ I`, so computing it on a subgraph needs every node one hop past `j`. Given a `κ` whose image
*contains* `ball A v (r + 1)`, the degree at `j`'s index survives restriction whenever `j` itself
only reaches out to radius `r`.

The direction needs `A`'s symmetry (`hSymm`), which `[1, §4.3]`'s undirected graph always has:
`ball` grows via `A i j` with `i` known, while a column sum for fixed `j` ranges over rows `i`.
Without `hSymm` the claim is false.

## Inputs
* `N` – number of nodes
* `A` – adjacency matrix
* `v` – center node
* `r` – radius in hops
* `K` – number of kept nodes
* `κ` – indices of the kept nodes
* `j` – node whose degree is read
* `k` – index of that node among the kept ones

## Hypotheses
* `_hA` – adjacency entries are nonnegative
* `hSymm` – adjacency matrix is symmetric
* `hinj` – kept indices are distinct
* `hκ` – kept nodes contain the ball one hop larger
* `hj` – node lies in the ball of radius r
* `hk` – index names the node

## Conclusion
* the degree on the subgraph equals the degree in the whole graph

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

/-- A degree computed on the subgraph a ball's `κ` enumerates agrees with the whole
graph's, at any node whose own ball reaches only one radius short. -/
theorem GNN.degree_submatrix_of_ball {N : ℕ} (A : Mat ℝ N N) (_hA : ∀ i j, 0 ≤ A i j)
    (hSymm : ∀ i j, A i j = A j i) (v : Fin N) (r : ℕ) {K : ℕ} (κ : Fin K → Fin N)
    (hinj : Function.Injective κ) (hκ : GNN.ball A v (r + 1) ⊆ Finset.univ.image κ)
    {j : Fin N} (hj : j ∈ GNN.ball A v r) (k : Fin K) (hk : κ k = j) : -- --- CONCL ---
    GNN.degree (A.submatrix κ κ) k = GNN.degree A j := by -- --- PROOF ---
  -- a nonzero row `i` puts `i` one hop past `j`, using the graph's own symmetry
  have hmem : ∀ i, (A + 1) i j ≠ 0 → i ∈ GNN.ball A v (r + 1) := by
    intro i hi
    rw [Matrix.add_apply] at hi
    by_cases heq : i = j
    · rw [heq]; exact GNN.ball_subset_succ A v r hj
    · have hAij : A i j ≠ 0 := fun h0 => hi (by simp [h0, Matrix.one_apply_ne heq])
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, j, hj, Or.inr ((hSymm i j) ▸ hAij)⟩
  -- so every contributing row already sits in `κ`'s image, and nothing outside it matters
  have hcut : ∑ i, (A + 1) i j = ∑ i ∈ Finset.univ.image κ, (A + 1) i j := by
    refine (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_).symm
    by_contra hne
    exact hi (hκ (hmem i hne))
  -- the identity's off-diagonal entries vanish, and injectivity keeps the diagonal intact
  have hterm : ∀ i : Fin K, (A.submatrix κ κ + 1) i k = (A + 1) (κ i) j := by
    intro i
    rw [← hk]
    by_cases h : i = k
    · simp [h, Matrix.add_apply, Matrix.submatrix_apply]
    · simp [Matrix.add_apply, Matrix.submatrix_apply, Matrix.one_apply_ne h,
        Matrix.one_apply_ne (fun hc => h (hinj hc))]
  show ∑ i, (A.submatrix κ κ + 1) i k = ∑ i, (A + 1) i j
  rw [hcut, Finset.sum_image hinj.injOn]
  exact Finset.sum_congr rfl fun i _ => hterm i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
