import CORALean.ContSet.ContSet.ContSet

/-!
# The row of ones a summation across nodes multiplies by

[1]'s `1`: the row vector, as a `1 × N` matrix, that `sumPoolLin_apply` reads
`sumPoolLin`'s column sum back against.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1]'s `1`: the row of ones a summation across nodes multiplies by. -/
def GNN.onesRow (N : ℕ) : Mat ℝ 1 N := fun _ _ => 1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
