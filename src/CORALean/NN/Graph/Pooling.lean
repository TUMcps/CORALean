import CORALean.ContSet.PolyZonotope.Real.Operations.Map

/-!
# Summation pooling across nodes

CORA's `nnGNNGlobalPoolingLayer` at the sum, and [1, Prop. 3]: `H ↦ (1 H)ᵀ`,
which aggregates the nodes away and leaves one feature vector for the graph.
Linear again, so its propagation is `PolyZonotope.map` and its guarantee
`map_exact`.

The result is a `Vec ℝ F` and not a `Mat ℝ F 1`, and that is the point of this
file beyond the arithmetic: pooling is where a graph network stops being
matrix-shaped, so landing in the ambient type `Layer` and `NeuralNetwork`
already use lets everything after the pooling be the ordinary vector-shaped
layers with no conversion in between.

`sumPoolLin_apply` is what ties the column sum back to [1]'s `1 H`, and the
exactness theorem is stated in that form so it can be read against the paper.

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

/-- [1]'s `1`: the row of ones a summation across nodes multiplies by. -/
def GNN.onesRow (N : ℕ) : Mat ℝ 1 N := fun _ _ => 1

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

/-- The column sum is [1]'s `1 H`, one row of ones being what reads it. -/
theorem GNN.sumPoolLin_apply (H : Mat ℝ N F) (j : Fin F) :
    GNN.sumPoolLin N F H j = (GNN.onesRow N * H) 0 j := by
  rw [Matrix.mul_apply]
  show ∑ i, H i j = ∑ i, GNN.onesRow N 0 i * H i j
  exact Finset.sum_congr rfl fun i _ => (one_mul (H i j)).symm


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Summation pooling on a matrix polynomial zonotope, landing in the vector
shape the layers after it read. -/
def GNN.sumPool (PZ : PolyZonotope (Mat ℝ N F)) : PolyZonotope (Vec ℝ F) :=
  PZ.map (GNN.sumPoolLin N F)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
