import CORALean.NN.Graph.Theorems.AdjAtSupportSubset
import CORALean.NN.Graph.Theorems.AdjAtSymm
import CORALean.NN.Graph.Theorems.BallMonoOfSupport
import CORALean.NN.Graph.Theorems.MessagePassingSubmatrixOfBall

/-!
# `[1, §4.3]`'s extra hop, for `messagePassing` itself, uniform in `lam`

`messagePassing_submatrix_of_ball` applied at `A := adjAt A U lam`, carried by the same
`adjAt_symm`/`adjAt_support_subset`/`ball_mono_of_support` composition
`DegreeSubmatrixOfBallUncertain` uses for `degree`. One `κ`, sized against `adjMax A U`
alone, serves every admissible `lam` at once — the piece `!179`'s `messagePassing`
locality was missing to reach the uncertain graph.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


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
    (hkj : κ kj = j) :
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
