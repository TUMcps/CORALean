module

public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# Zeroing everything outside a set of nodes

`mask S P` is `P` with every entry not between two nodes of `S` replaced by
`0`. It is the vehicle for `[1, §4.3]`'s locality: `EvalStepsRowMask` says that
once `S` contains a ball large enough, masking outside it does not change the
ball's own row of an `evalSteps` chain.

## Inputs
* `S` – set of nodes to keep
* `P` – message-passing matrix

## Output
* matrix with every entry outside the kept nodes zeroed

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph Convolutional Networks
      with Uncertain Node Features and Uncertain Graph Structure". Transactions on Machine Learning
      Research, 2025.
-/

-- Authors:       Claude Sonnet 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `P` restricted to `S`: an entry survives only when both its row and its
column name a node of `S`, and is `0` otherwise. -/
noncomputable def GNN.mask (S : Finset (Fin N)) (P : Mat ℝ N N) : Mat ℝ N N :=
  fun i j => if i ∈ S ∧ j ∈ S then P i j else 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
