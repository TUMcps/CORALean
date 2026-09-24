import CORALean.NN.Graph.Operations.OnesRow
import CORALean.NN.Graph.Operations.SumPoolLin

/-!
# `sumPoolLin` unfolds to `[1]`'s `1 H`

`sumPoolLin_apply` is what ties the column sum back to [1]'s `1 H`, stated in
that form so it can be read against the paper.

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

variable {N F : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The column sum is [1]'s `1 H`, one row of ones being what reads it. -/
theorem GNN.sumPoolLin_apply (H : Mat ℝ N F) (j : Fin F) :
    GNN.sumPoolLin N F H j = (GNN.onesRow N * H) 0 j := by
  rw [Matrix.mul_apply]
  show ∑ i, H i j = ∑ i, GNN.onesRow N 0 i * H i j
  exact Finset.sum_congr rfl fun i _ => (one_mul (H i j)).symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
