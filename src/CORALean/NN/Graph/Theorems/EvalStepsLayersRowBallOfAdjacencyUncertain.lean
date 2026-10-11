import CORALean.NN.Graph.Theorems.EvalStepsLayersRowBallEnum
import CORALean.NN.Graph.Theorems.MessagePassingSubmatrixOfBallUncertain

/-!
# `[1, Sec. 4.3]`'s locality for the layered network, uniform in the graph's uncertainty

The network with its activations, end to end: row `v` of `L` message-passing steps with a
per-node layer after each, at any admissible weighting `adjAt A U lam` of the uncertain edges, is
computable from `adjMax A U`'s own `(L + 1)`-ball alone — the subgraph a breadth-first search from
`v` over every uncertain edge finds, message passing computed on that subgraph's own adjacency.
`evalSteps_row_ball_of_adjacency_uncertain` with a layer after each step.

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

/-- Row `v` of an `L`-step layered chain on `messagePassing (adjAt A U lam)` is computable from
`adjMax A U`'s own `(L + 1)`-ball alone, uniformly in every admissible `lam` at once. -/
theorem GNN.evalStepsLayers_row_ball_of_adjacency_uncertain {N F m : ℕ} (A : Mat ℝ N N)
    (U : Fin m → Fin N × Fin N) (hA : ∀ i j, 0 ≤ A i j) (hSymm : ∀ i j, A i j = A j i)
    {lam : Fin m → ℝ} (hlam : ∀ e, 0 ≤ lam e ∧ lam e ≤ 1) (v : Fin N) (L : ℕ) {K : ℕ}
    (κ : Fin K → Fin N) (hinj : Function.Injective κ)
    (hκ : GNN.ball (GNN.adjMax A U) v (L + 1) ⊆ Finset.univ.image κ)
    (g : Fin L → Vec ℝ F → Vec ℝ F) (X : Mat ℝ N F) :
    ∃ φ : Fin (GNN.ball (GNN.adjAt A U lam) v L).card → Fin K,
      GNN.evalStepsLayers (GNN.messagePassing (GNN.adjAt A U lam)) L g X v
        = GNN.evalStepsLayers
            ((GNN.messagePassing ((GNN.adjAt A U lam).submatrix κ κ)).submatrix φ φ) L
            g ((X.submatrix κ id).submatrix φ id)
            (GNN.ballEnumIdx (GNN.adjAt A U lam) v L) := by -- --- PROOF ---
  -- every node the inner ball enumerates also sits in `adjMax A U`'s `(L + 1)`-ball
  have hmemL : ∀ k : Fin (GNN.ball (GNN.adjAt A U lam) v L).card,
      GNN.ballEnum (GNN.adjAt A U lam) v L k ∈ GNN.ball (GNN.adjAt A U lam) v L :=
    fun k => (GNN.mem_ballEnum_iff (GNN.adjAt A U lam) v L _).mp ⟨k, rfl⟩
  have hmono : GNN.ball (GNN.adjAt A U lam) v (L + 1) ⊆ GNN.ball (GNN.adjMax A U) v (L + 1) :=
    GNN.ball_mono_of_support (fun i j => GNN.adjAt_support_subset A U hA hlam i j) v (L + 1)
  have hex : ∀ k : Fin (GNN.ball (GNN.adjAt A U lam) v L).card,
      ∃ l, κ l = GNN.ballEnum (GNN.adjAt A U lam) v L k := fun k =>
    Finset.mem_image.mp (hκ (hmono (GNN.ball_subset_succ (GNN.adjAt A U lam) v L (hmemL k))))
      |>.imp fun _ h => h.2
  choose φ hφκ using hex
  refine ⟨φ, ?_⟩
  -- `messagePassing` agrees pointwise on the inner ball, read off `adjAt A U lam`'s own submatrix
  have hP : (GNN.messagePassing (GNN.adjAt A U lam)).submatrix
      (GNN.ballEnum (GNN.adjAt A U lam) v L) (GNN.ballEnum (GNN.adjAt A U lam) v L)
      = (GNN.messagePassing ((GNN.adjAt A U lam).submatrix κ κ)).submatrix φ φ := by
    funext k k'
    simp only [Matrix.submatrix_apply]
    exact (GNN.messagePassing_submatrix_of_ball_uncertain A U hA hSymm hlam v L κ hinj hκ
      (hmemL k) (hmemL k') (φ k) (φ k') (hφκ k) (hφκ k')).symm
  have hX : X.submatrix (GNN.ballEnum (GNN.adjAt A U lam) v L) id
      = (X.submatrix κ id).submatrix φ id := by
    funext k f
    simp [Matrix.submatrix_apply, hφκ k]
  rw [GNN.evalStepsLayers_row_ball_enum (GNN.adjAt A U lam) v L g X, hP, hX]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
