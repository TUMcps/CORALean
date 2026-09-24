import CORALean.NN.Graph.Operations.Select

/-!
# `select` multiplies out to row selection

`H' = M H` is plain row selection, `Matrix.submatrix`, so `[1, Cor. 1]`'s projection
costs nothing to state.

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

variable {N K F : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem GNN.select_mul (κ : Fin K → Fin N) (H : Mat ℝ N F) :
    GNN.select κ * H = H.submatrix κ id := by
  funext k j
  show ∑ i, (1 : Mat ℝ N N) (κ k) i * H i j = H (κ k) j
  simp [Matrix.one_apply]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
