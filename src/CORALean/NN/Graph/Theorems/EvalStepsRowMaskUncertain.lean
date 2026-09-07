import CORALean.NN.Graph.Theorems.AdjAtSupportSubset
import CORALean.NN.Graph.Theorems.BallMonoOfSupport
import CORALean.NN.Graph.Theorems.EvalStepsRowMask

/-!
# `[1, §4.3]`'s locality, uniform in the graph's own uncertainty

Not `evalSteps_row_ball`: that theorem's `hκ` asks `κ`'s image to be *exactly*
`ball A v L`, and the ball an admissible `adjAt A U lam` grows is graph-specific
— it need not equal `ball (adjMax A U) v L` at any `lam` other than the one
pinning every weight to `1`. `evalSteps_row_mask`'s `hS` is only an *inclusion*,
which composes: `ball (adjAt A U lam) v L ⊆ ball (adjMax A U) v L` by
`ball_mono_of_support`/`adjAt_support_subset`, so any `S` already large enough
for `adjMax A U` is large enough for every admissible `adjAt A U lam` at once.

One `S`, sized against `adjMax A U`, therefore serves every `lam` — the
subgraph reduction a caller already had at a known graph carries over to an
uncertain one, uniformly.

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

variable {N F m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Masking to a set large enough for `adjMax A U`'s ball leaves the centre's row
untouched at every admissible `lam`, given the two inputs already agree there. -/
theorem GNN.evalSteps_row_mask_uncertain (A : Mat ℝ N N) (U : Fin m → Fin N × Fin N)
    (hA : ∀ i j, 0 ≤ A i j) {lam : Fin m → ℝ} (hlam : ∀ e, 0 ≤ lam e ∧ lam e ≤ 1) (v : Fin N)
    (S : Finset (Fin N)) (L : ℕ) (hS : GNN.ball (GNN.adjMax A U) v L ⊆ S)
    (W : Fin L → Mat ℝ F F) (X Y : Mat ℝ N F)
    (hXY : ∀ u ∈ GNN.ball (GNN.adjMax A U) v L, X u = Y u) :
    GNN.evalSteps (GNN.messagePassing (GNN.adjAt A U lam)) L W X v
      = GNN.evalSteps (GNN.mask S (GNN.messagePassing (GNN.adjAt A U lam)))
          L W Y v := by
  have hmono : GNN.ball (GNN.adjAt A U lam) v L ⊆ GNN.ball (GNN.adjMax A U) v L :=
    GNN.ball_mono_of_support (fun i j => GNN.adjAt_support_subset A U hA hlam i j) v L
  exact GNN.evalSteps_row_mask (GNN.adjAt A U lam) v S L (hmono.trans hS) W X Y
    (fun u hu => hXY u (hmono hu))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
