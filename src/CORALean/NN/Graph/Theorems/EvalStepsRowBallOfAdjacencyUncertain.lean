module

public import CORALean.NN.Graph.Theorems.EvalStepsRowBallEnum
public import CORALean.NN.Graph.Theorems.MessagePassingSubmatrixOfBallUncertain

@[expose] public section

/-!
# `[1, §4.3]`'s locality, end to end, uniform in the graph's own uncertainty

`evalSteps_row_ball_enum` asks nothing of its adjacency, so it runs at `adjAt A U lam` itself,
reducing row `v` to *its own* `L`-ball, not `adjMax A U`'s. That inner enumeration embeds into a
`κ` sized against `adjMax A U`'s `(L + 1)`-ball via `messagePassing_submatrix_of_ball_uncertain`
— the same `φ`, the same reason `EvalStepsRowBallOfAdjacency` keeps it existential. `mask`
(`EvalStepsRowMaskUncertain`) never enters: it sizes `S` against `adjMax A U` too, but that is
looser than `adjAt A U lam`'s own ball, so a masked entry need not match the submatrix built from
`adjAt A U lam` pointwise; the exact enumeration is what a caller actually needs here.

## Inputs
* `N` – number of nodes
* `F` – feature width
* `m` – number of uncertain edges
* `A` – adjacency matrix
* `U` – uncertain edges
* `lam` – weights of the uncertain edges
* `v` – node of interest
* `L` – number of steps
* `K` – number of kept nodes
* `κ` – indices of the kept nodes
* `W` – weights of the steps
* `X` – node-feature matrix

## Hypotheses
* `hA` – adjacency entries are nonnegative
* `hSymm` – adjacency matrix is symmetric
* `hlam` – edge weights lie in the unit interval
* `hinj` – kept indices are distinct
* `hκ` – kept nodes contain the maximal ball one hop larger

## Conclusion
* the node's row is computable on a subgraph of the kept nodes

## References

* [1] [T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph Convolutional Networks
      with Uncertain Node Features and Uncertain Graph Structure". Transactions on Machine Learning
      Research, 2025.](../../../../../references/2025/ladner-tmlr-gcn.md)
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- Row `v` of an `L`-step chain on `messagePassing (adjAt A U lam)` is computable from `adjMax
A U`'s own `(L + 1)`-ball alone, uniformly in every admissible `lam` at once. -/
theorem GNN.evalSteps_row_ball_of_adjacency_uncertain {N F m : ℕ} (A : Mat ℝ N N)
    (U : Fin m → Fin N × Fin N) (hA : ∀ i j, 0 ≤ A i j) (hSymm : ∀ i j, A i j = A j i)
    {lam : Fin m → ℝ} (hlam : ∀ e, 0 ≤ lam e ∧ lam e ≤ 1) (v : Fin N) (L : ℕ) {K : ℕ}
    (κ : Fin K → Fin N) (hinj : Function.Injective κ)
    (hκ : GNN.ball (GNN.adjMax A U) v (L + 1) ⊆ Finset.univ.image κ)
    (W : Fin L → Mat ℝ F F) (X : Mat ℝ N F) : -- --- CONCL ---
    ∃ φ : Fin (GNN.ball (GNN.adjAt A U lam) v L).card → Fin K,
      GNN.evalSteps (GNN.messagePassing (GNN.adjAt A U lam)) L W X v
        = GNN.evalSteps ((GNN.messagePassing ((GNN.adjAt A U lam).submatrix κ κ)).submatrix φ φ) L
            W ((X.submatrix κ id).submatrix φ id)
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
  rw [GNN.evalSteps_row_ball_enum (GNN.adjAt A U lam) v L W X, hP, hX]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
