module

public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# Summation pooling as one linear map

CORA's `nnGNNGlobalPoolingLayer` at the sum — [1, Def. 5]: each feature summed
across the nodes, `H ↦ (1 H)ᵀ` read as a linear map `Mat ℝ N F →ₗ[ℝ] Vec ℝ F`.

The result is a `Vec ℝ F` and not a `Mat ℝ F 1`, and that is the point of this
file beyond the arithmetic: pooling is where a graph network stops being
matrix-shaped, so landing in the ambient type `Layer` and `NeuralNetwork`
already use lets everything after the pooling be the ordinary vector-shaped
layers with no conversion in between.

## Inputs
* `N` – number of nodes
* `F` – feature width

## Output
* linear map summing every feature over the nodes

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

variable {N F : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Each feature summed across the nodes. -/
def GNN.sumPoolLin (N F : ℕ) : Mat ℝ N F →ₗ[ℝ] Vec ℝ F where
  toFun H := fun j => ∑ i, H i j
  map_add' H K := by
    funext j
    show ∑ i, (H i j + K i j) = (∑ i, H i j) + ∑ i, K i j
    exact Finset.sum_add_distrib
  map_smul' c H := by
    funext j
    show ∑ i, c * H i j = c * ∑ i, H i j
    rw [Finset.mul_sum]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
