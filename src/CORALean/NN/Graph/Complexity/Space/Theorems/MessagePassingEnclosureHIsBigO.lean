module

public import CORALean.NN.Graph.Operations.MessagePassingEnclosure
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Tactic.Positivity
public import CORALean.NN.Graph.Complexity.Space.Theorems.MessagePassingEnclosureHLe

@[expose] public section

/-!
# `GNN.messagePassingEnclosure_h_isBigO`

The enclosure of [1, Prop. 4] grows cubically in the number of uncertain
edges, at a fixed graph size.

## Inputs
* `R` – relaxation of the square root
* `A` – adjacency matrix
* `U` – uncertain edges for each edge count

## Hypotheses
* none

## Conclusion
* the enclosure's generator count is big-O of the cube of the edge count

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph Convolutional Networks
      with Uncertain Node Features and Uncertain Graph Structure". Transactions on Machine Learning
      Research, 2025.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   13-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The enclosure of [1, Prop. 4] grows cubically in the number of uncertain
edges, at a fixed graph size. -/
theorem GNN.messagePassingEnclosure_h_isBigO (R : Relaxation ℝ) (A : Mat ℝ N N)
    (U : ∀ m : ℕ, Fin m → Fin N × Fin N) : -- --- CONCL ---
    (fun m : ℕ => (((GNN.messagePassingEnclosure R A (U m)).h : ℕ) : ℝ))
      =O[Filter.atTop] fun m : ℕ => (m : ℝ) ^ 3 := by -- --- PROOF ---
  apply Asymptotics.IsBigO.of_bound ((((N + 2) * (N + 2) + 1) * (N + 2) : ℕ) : ℝ)
  filter_upwards [Filter.eventually_ge_atTop 1] with m hm
  -- the bound is a statement about naturals, so the cast is the last step
  have h := GNN.messagePassingEnclosure_h_le R A (U m) hm
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  exact_mod_cast h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
