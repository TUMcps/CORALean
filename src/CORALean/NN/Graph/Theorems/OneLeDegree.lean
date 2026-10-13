import CORALean.NN.Graph.Operations.Degree
import Mathlib.Tactic.Linarith

/-!
# A degree is never below one

The self-loop is what keeps a degree away from zero, so `messagePassing`
divides by nothing that can vanish on a nonnegative adjacency — the same fact
an uncertain degree's inverse square root needs in order to stay away from
zero.
-/

-- Authors:       Claude Sonnet 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The self-loop is what keeps a degree away from zero, so `messagePassing`
divides by nothing that can vanish on a nonnegative adjacency. -/
theorem GNN.one_le_degree (A : Mat ℝ N N) (hA : ∀ i j, 0 ≤ A i j) (j : Fin N) :
    1 ≤ GNN.degree A j := by -- --- PROOF ---
  -- the identity contributes the self-loop, and the adjacency only adds to it
  have hsplit : GNN.degree A j = (∑ i, A i j) + ∑ i, (1 : Mat ℝ N N) i j := by
    simp only [GNN.degree, Matrix.add_apply, Finset.sum_add_distrib]
  have hone : ∑ i, (1 : Mat ℝ N N) i j = 1 := by
    simp only [Matrix.one_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hnn : 0 ≤ ∑ i, A i j := Finset.sum_nonneg fun i _ => hA i j
  rw [hsplit, hone]
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
