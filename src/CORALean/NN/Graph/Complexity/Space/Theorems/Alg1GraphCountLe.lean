module

public import CORALean.NN.Graph.Complexity.Space.Theorems.Alg1NodeEqGcnActSteps
public import CORALean.NN.Graph.Complexity.Space.Theorems.Alg1NodeHLe
public import CORALean.NN.Graph.Complexity.Space.Theorems.GcnActStepsQ
public import CORALean.NN.Graph.Complexity.Space.Theorems.Basic
public import CORALean.NN.Graph.Complexity.Space.Theorems.TailEncloseCountLe
public import CORALean.NN.Graph.Operations.Alg1Graph

@[expose] public section

/-!
# `Alg. 1`'s count for a graph-level output

[1, Thm. 1 (generators)]: the graph layers leave `K^κ' m^(3κ') (h_x + 1 + κ' ν)` generators
(`alg1Node_h_le`), the pooling and the linear layers leave the count alone and an activation after
the pooling adds at most its neurons ([1, Prop. 1]), so the tail adds at most the sum of what its
layers do (`tailEnclose_count_le`). With `n_k` the neurons of the activation layers and `n_max` the
most of them, that sum is at most `(κ - 2κ') n_max`.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1 (generators)]: the generators of `Alg. 1`'s output, dependent and independent, number
at most the graph layers' plus what the standard layers after the pooling add. -/
theorem GNN.alg1Graph_count_le (R : Relaxation ℝ) (A : Mat ℝ N N) (U : Fin m → Fin N × Fin N)
    (hm : 1 ≤ m) (L T : ℕ) (c : ℕ → ℕ) (W : ∀ s, Mat ℝ (c s) (c (s + 1)))
    (acts : ∀ s, GNN.ActLayer N (c (s + 1))) (ν : ℕ) (hadd : ∀ s, s < L → (acts s).AddsAtMost ν)
    (f : ∀ t, PolyZonotope (Vec ℝ (c (L + t))) → PolyZonotope (Vec ℝ (c (L + (t + 1)))))
    (e : ℕ → ℕ) (hf : ∀ t S, (f t S).h + (f t S).q ≤ S.h + S.q + e t)
    (X : PolyZonotope (Mat ℝ N (c 0))) : -- --- STMT ---
    (GNN.alg1Graph R A U L T c W acts f X).h + (GNN.alg1Graph R A U L T c W acts f X).q + 1
      ≤ (((N + 2) * (N + 2) + 1) * (N + 2) + 2) ^ L * m ^ (3 * L) * (X.h + X.q + 1 + L * ν)
        + ∑ t ∈ Finset.range T, e t := by -- --- PROOF ---
  -- the graph layers leave no independent generators, so the pooled set has `h` alone
  have hq : (GNN.alg1Node R A U L c W acts X).q = 0 := by
    rw [GNN.alg1Node_eq_gcnActSteps]
    exact GNN.gcnActSteps_q L c W acts _ _ rfl rfl
  have hnode := GNN.alg1Node_h_le R A U hm L c W acts ν hadd X
  have htail := GNN.tailEnclose_count_le T (fun t => c (L + t)) f e hf
    (GNN.sumPool (GNN.alg1Node R A U L c W acts X))
  show (GNN.tailEnclose T (fun t => c (L + t)) f
      (GNN.sumPool (GNN.alg1Node R A U L c W acts X))).h
    + (GNN.tailEnclose T (fun t => c (L + t)) f
      (GNN.sumPool (GNN.alg1Node R A U L c W acts X))).q + 1 ≤ _
  simp only [GNN.sumPool_h, GNN.sumPool_q, hq] at htail
  omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
