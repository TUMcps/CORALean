module

public import CORALean.NN.Graph.Operations.Select

@[expose] public section

/-!
# `select` multiplies out to row selection

`H' = M H` is plain row selection, `Matrix.submatrix`, so `[1, Cor. 1]`'s projection
costs nothing to state.

## Inputs
* `κ` – indices of the selected nodes
* `H` – node-feature matrix

## Hypotheses
* none

## Conclusion
* the selection matrix picks the selected rows

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

variable {N K F : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem GNN.select_mul (κ : Fin K → Fin N) (H : Mat ℝ N F) :
    GNN.select κ * H = H.submatrix κ id := by
  funext k j
  show ∑ i, (1 : Mat ℝ N N) (κ k) i * H i j = H (κ k) j
  simp [Matrix.one_apply]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
