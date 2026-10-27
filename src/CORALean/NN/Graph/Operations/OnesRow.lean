module

public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# The row of ones a summation across nodes multiplies by

[1]'s `1`: the row vector, as a `1 × N` matrix, that `sumPoolLin_apply` reads
`sumPoolLin`'s column sum back against.

## Inputs
* `N` – number of nodes

## Output
* row of ones

## References

* [1] [T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph Convolutional Networks
      with Uncertain Node Features and Uncertain Graph Structure". Transactions on Machine Learning
      Research, 2025.](../../../../../references/2025/ladner-tmlr-gcn.md)
-/

-- Authors:       Claude Sonnet 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1]'s `1`: the row of ones a summation across nodes multiplies by. -/
def GNN.onesRow (N : ℕ) : Mat ℝ 1 N := fun _ _ => 1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
