module

public import CORALean.NN.Graph.Theorems.AdjAtSupportSubset
public import CORALean.NN.Graph.Theorems.AdjAtSymm
public import CORALean.NN.Graph.Theorems.BallMonoOfSupport
public import CORALean.NN.Graph.Theorems.MessagePassingSubmatrixOfBall

@[expose] public section

/-!
# `[1, §4.3]`'s extra hop, for `messagePassing` itself, uniform in `lam`

`messagePassing_submatrix_of_ball` applied at `A := adjAt A U lam`, carried by the same
`adjAt_symm`/`adjAt_support_subset`/`ball_mono_of_support` composition
`DegreeSubmatrixOfBallUncertain` uses for `degree`. One `κ`, sized against `adjMax A U`
alone, serves every admissible `lam` at once — the piece `!179`'s `messagePassing`
locality was missing to reach the uncertain graph.

## Inputs
* `N` – number of nodes
* `m` – number of uncertain edges
* `A` – adjacency matrix
* `U` – uncertain edges
* `lam` – weights of the uncertain edges
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
* `hlam` – edge weights lie in the unit interval
* `hinj` – kept indices are distinct
* `hκ` – kept nodes contain the maximal ball one hop larger
* `hi` – first node lies in the ball of radius r
* `hj` – second node lies in the ball of radius r
* `hki` – index names the first node
* `hkj` – index names the second node

## Conclusion
* the message on the subgraph equals the message in the whole uncertain graph

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph Convolutional Networks
      with Uncertain Node Features and Uncertain Graph Structure". Transactions on Machine Learning
      Research, 2025.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- Message passing computed on the subgraph a ball's `κ` enumerates agrees with the
whole uncertain graph's, between any two nodes whose own `adjAt A U lam`-balls reach
only one radius short — uniformly in `lam`. -/
theorem GNN.messagePassing_submatrix_of_ball_uncertain {N m : ℕ} (A : Mat ℝ N N)
    (U : Fin m → Fin N × Fin N) (hA : ∀ i j, 0 ≤ A i j) (hSymm : ∀ i j, A i j = A j i)
    {lam : Fin m → ℝ} (hlam : ∀ e, 0 ≤ lam e ∧ lam e ≤ 1) (v : Fin N) (r : ℕ) {K : ℕ}
    (κ : Fin K → Fin N) (hinj : Function.Injective κ)
    (hκ : GNN.ball (GNN.adjMax A U) v (r + 1) ⊆ Finset.univ.image κ)
    {i j : Fin N} (hi : i ∈ GNN.ball (GNN.adjAt A U lam) v r)
    (hj : j ∈ GNN.ball (GNN.adjAt A U lam) v r) (ki kj : Fin K) (hki : κ ki = i)
    (hkj : κ kj = j) : -- --- CONCL ---
    GNN.messagePassing ((GNN.adjAt A U lam).submatrix κ κ) ki kj
      = GNN.messagePassing (GNN.adjAt A U lam) i j := by -- --- PROOF ---
  have hAnn : ∀ p q, 0 ≤ GNN.adjAt A U lam p q := fun p q => by
    simp only [GNN.adjAt, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    have h : 0 ≤ ∑ e, lam e * GNN.edgeMat (U e) p q :=
      Finset.sum_nonneg fun e _ => mul_nonneg (hlam e).1 (GNN.edgeMat_nonneg (U e) p q)
    linarith [hA p q]
  have hmono : GNN.ball (GNN.adjAt A U lam) v (r + 1) ⊆ GNN.ball (GNN.adjMax A U) v (r + 1) :=
    GNN.ball_mono_of_support (fun p q => GNN.adjAt_support_subset A U hA hlam p q) v (r + 1)
  exact GNN.messagePassing_submatrix_of_ball (GNN.adjAt A U lam) hAnn (GNN.adjAt_symm A U hSymm lam)
    v r κ hinj (hmono.trans hκ) hi hj ki kj hki hkj

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
