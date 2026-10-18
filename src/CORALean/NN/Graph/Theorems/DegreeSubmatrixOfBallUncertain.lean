module

public import CORALean.NN.Graph.Theorems.AdjAtSupportSubset
public import CORALean.NN.Graph.Theorems.AdjAtSymm
public import CORALean.NN.Graph.Theorems.BallMonoOfSupport
public import CORALean.NN.Graph.Theorems.DegreeSubmatrixOfBall

@[expose] public section

/-!
# `[1, §4.3]`'s extra hop, uniform in the graph's own uncertainty

`degree_submatrix_of_ball` applied at `A := adjAt A U lam`: `adjAt_symm` supplies the
symmetry it needs, and `adjAt_support_subset`/`ball_mono_of_support` carry its (now
inclusion-only) `hκ` from `adjMax A U`'s ball down to `adjAt A U lam`'s — the same
composition `EvalStepsRowMaskUncertain` uses for its `hS`. One `κ`, sized against
`adjMax A U` alone, therefore serves every admissible `lam` at once.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- A degree computed on the subgraph a ball's `κ` enumerates agrees with the whole
uncertain graph's, at any node whose own `adjAt A U lam`-ball reaches only one radius
short — uniformly in `lam`, given `κ`'s image contains `adjMax A U`'s `(r + 1)`-ball. -/
theorem GNN.degree_submatrix_of_ball_uncertain {N m : ℕ} (A : Mat ℝ N N)
    (U : Fin m → Fin N × Fin N) (hA : ∀ i j, 0 ≤ A i j) (hSymm : ∀ i j, A i j = A j i)
    {lam : Fin m → ℝ} (hlam : ∀ e, 0 ≤ lam e ∧ lam e ≤ 1) (v : Fin N) (r : ℕ) {K : ℕ}
    (κ : Fin K → Fin N) (hinj : Function.Injective κ)
    (hκ : GNN.ball (GNN.adjMax A U) v (r + 1) ⊆ Finset.univ.image κ)
    {j : Fin N} (hj : j ∈ GNN.ball (GNN.adjAt A U lam) v r) (k : Fin K)
    (hk : κ k = j) : -- --- STMT ---
    GNN.degree ((GNN.adjAt A U lam).submatrix κ κ) k
      = GNN.degree (GNN.adjAt A U lam) j := by -- --- PROOF ---
  have hAnn : ∀ p q, 0 ≤ GNN.adjAt A U lam p q := fun p q => by
    simp only [GNN.adjAt, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    have h : 0 ≤ ∑ e, lam e * GNN.edgeMat (U e) p q :=
      Finset.sum_nonneg fun e _ => mul_nonneg (hlam e).1 (GNN.edgeMat_nonneg (U e) p q)
    linarith [hA p q]
  have hmono : GNN.ball (GNN.adjAt A U lam) v (r + 1) ⊆ GNN.ball (GNN.adjMax A U) v (r + 1) :=
    GNN.ball_mono_of_support (fun p q => GNN.adjAt_support_subset A U hA hlam p q) v (r + 1)
  exact GNN.degree_submatrix_of_ball (GNN.adjAt A U lam) hAnn (GNN.adjAt_symm A U hSymm lam) v r
    κ hinj (hmono.trans hκ) hj k hk

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
