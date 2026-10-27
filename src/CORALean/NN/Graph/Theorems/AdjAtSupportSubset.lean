module

public import CORALean.NN.Graph.Operations.AdjMax
public import CORALean.NN.Graph.Theorems.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The maximal adjacency's support dominates every admissible one

Both `A i j` and every edge's weighted contribution are nonnegative at an admissible `lam`, so
`adjAt A U lam i j` sits between `0` and `adjMax A U i j`. A nonzero entry is then a positive one,
forced below a positive `adjMax A U i j` — the fact `[1, §4.3]`'s uncertain-graph half of subgraph
reduction rests on.

**The nonnegativity hypotheses are load-bearing.** Without them a negative entry could cancel
against another term, vanishing at one `lam` and not at `fun _ => 1`, and no containment of supports
would hold.

## Inputs
* `A` – adjacency matrix
* `U` – uncertain edges
* `lam` – weights of the uncertain edges
* `i` – row node
* `j` – column node

## Hypotheses
* `hA` – adjacency entries are nonnegative
* `hlam` – edge weights lie in the unit interval

## Conclusion
* a nonzero entry of the weighted adjacency is nonzero in the maximal one

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

variable {N m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A nonzero entry of an admissible `adjAt` is a nonzero entry of `adjMax`. -/
theorem GNN.adjAt_support_subset (A : Mat ℝ N N) (U : Fin m → Fin N × Fin N)
    (hA : ∀ i j, 0 ≤ A i j) {lam : Fin m → ℝ} (hlam : ∀ e, 0 ≤ lam e ∧ lam e ≤ 1)
    (i j : Fin N) : -- --- CONCL ---
    GNN.adjAt A U lam i j ≠ 0 → GNN.adjMax A U i j ≠ 0 := by -- --- PROOF ---
  have hle : GNN.adjAt A U lam i j ≤ GNN.adjMax A U i j := by
    simp only [GNN.adjMax, GNN.adjAt, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, one_mul]
    gcongr with e _
    exact mul_le_of_le_one_left (GNN.edgeMat_nonneg (U e) i j) (hlam e).2
  have hnn : 0 ≤ GNN.adjAt A U lam i j := by
    simp only [GNN.adjAt, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    have h : 0 ≤ ∑ e, lam e * GNN.edgeMat (U e) i j :=
      Finset.sum_nonneg fun e _ => mul_nonneg (hlam e).1 (GNN.edgeMat_nonneg (U e) i j)
    linarith [hA i j]
  intro hne
  exact ne_of_gt (lt_of_lt_of_le (hnn.lt_of_ne (Ne.symm hne)) hle)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
