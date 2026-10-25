module

public import CORALean.NN.Graph.Theorems.EvalStepsRowBallEnum
public import CORALean.NN.Graph.Theorems.MessagePassingSubmatrixOfBall

@[expose] public section

/-!
# `[1, §4.3]`'s locality, end to end: row `v` needs only `A`'s own `(L + 1)`-ball

The two halves composed: `evalSteps_row_ball_enum` reduces row `v` to the `L`-ball of an
*already-computed* `messagePassing A`, and `messagePassing_submatrix_of_ball` says that ball's
own entries are exactly what `messagePassing` gives back from `A.submatrix κ κ` alone — no need
to have touched the rest of `A` at all. `φ` embeds the inner ball's own enumeration into `κ`'s;
it is existentially packaged rather than exposed as data, being an artifact of *which* two
enumerations a caller happened to build, not a choice they made.

## Inputs
* `N` – number of nodes
* `F` – feature width
* `A` – adjacency matrix
* `v` – node of interest
* `L` – number of steps
* `K` – number of kept nodes
* `κ` – indices of the kept nodes
* `W` – weights of the steps
* `X` – node-feature matrix

## Hypotheses
* `hA` – adjacency entries are nonnegative
* `hSymm` – adjacency matrix is symmetric
* `hinj` – kept indices are distinct
* `hκ` – kept nodes contain the ball one hop larger

## Conclusion
* the node's row is computable on a subgraph of the kept nodes

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph Convolutional Networks
      with Uncertain Node Features and Uncertain Graph Structure". Transactions on Machine Learning
      Research, 2025.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   07-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- Row `v` of an `L`-step chain is computable from `A`'s own `(L + 1)`-ball alone: run
`messagePassing` on that submatrix, then restrict once more to the `L`-ball inside it. -/
theorem GNN.evalSteps_row_ball_of_adjacency {N F : ℕ} (A : Mat ℝ N N) (hA : ∀ i j, 0 ≤ A i j)
    (hSymm : ∀ i j, A i j = A j i) (v : Fin N) (L : ℕ) {K : ℕ} (κ : Fin K → Fin N)
    (hinj : Function.Injective κ) (hκ : GNN.ball A v (L + 1) ⊆ Finset.univ.image κ)
    (W : Fin L → Mat ℝ F F) (X : Mat ℝ N F) : -- --- CONCL ---
    ∃ φ : Fin (GNN.ball A v L).card → Fin K,
      GNN.evalSteps (GNN.messagePassing A) L W X v
        = GNN.evalSteps ((GNN.messagePassing (A.submatrix κ κ)).submatrix φ φ) L W
            ((X.submatrix κ id).submatrix φ id) (GNN.ballEnumIdx A v L) := by -- --- PROOF ---
  -- every node the inner ball enumerates also sits in the outer `(L + 1)`-ball
  have hmemL : ∀ k : Fin (GNN.ball A v L).card, GNN.ballEnum A v L k ∈ GNN.ball A v L :=
    fun k => (GNN.mem_ballEnum_iff A v L _).mp ⟨k, rfl⟩
  have hex : ∀ k : Fin (GNN.ball A v L).card, ∃ l, κ l = GNN.ballEnum A v L k := fun k =>
    Finset.mem_image.mp (hκ (GNN.ball_subset_succ A v L (hmemL k)))
      |>.imp fun _ h => h.2
  choose φ hφκ using hex
  refine ⟨φ, ?_⟩
  -- `messagePassing` agrees pointwise on the inner ball, read off `A`'s own outer submatrix
  have hP : (GNN.messagePassing A).submatrix (GNN.ballEnum A v L) (GNN.ballEnum A v L)
      = (GNN.messagePassing (A.submatrix κ κ)).submatrix φ φ := by
    funext k k'
    simp only [Matrix.submatrix_apply]
    exact (GNN.messagePassing_submatrix_of_ball A hA hSymm v L κ hinj hκ
      (hmemL k) (hmemL k') (φ k) (φ k') (hφκ k) (hφκ k')).symm
  have hX : X.submatrix (GNN.ballEnum A v L) id = (X.submatrix κ id).submatrix φ id := by
    funext k f
    simp [Matrix.submatrix_apply, hφκ k]
  rw [GNN.evalSteps_row_ball_enum A v L W X, hP, hX]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
