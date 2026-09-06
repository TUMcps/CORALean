import CORALean.ContSet.ContSet.ContSet
import CORALean.ContSet.PolyZonotope.Real.Operations.Map

/-!
# The graph convolutional layer, at a fixed graph

CORA's `nnGCNLayer` and [1, Prop. 2]: `H ↦ P H W` with the message passing
`P = D̃^(-1/2) Ã D̃^(-1/2)` of [2, Eq. 2]. The layer *is* a linear map of
matrices, so its propagation is `PolyZonotope.map` at that map and nothing else,
which is what makes `Theorems/ConvExact` a corollary of `map_exact` — and why
[1] records that this layer induces no outer approximation.

`P` and `W` stay separate arguments rather than one composed matrix: an
uncertain graph replaces `P` by an enclosure and leaves `W` alone, and the
exactness proof never reads either.

`degree` reads [1]'s `diag(1 Ã)` as column sums; for the symmetric adjacency a
graph convolution uses, rows and columns agree. `one_le_degree` is what makes
the division total — the self-loop in `Ã = A + I` puts every degree at 1 or
above — and it is the same fact an uncertain degree's inverse square root needs
in order to stay away from zero.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025.
* [2] T. N. Kipf and M. Welling. "Semi-Supervised Classification with Graph
      Convolutional Networks". ICLR, 2017.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N F₁ F₂ : ℕ}

/-- Node `j`'s degree in `Ã = A + I`, which is `diag(1 Ã)` read as a function. -/
def GNN.degree (A : Mat ℝ N N) (j : Fin N) : ℝ := ∑ i, (A + 1) i j

/-- The self-loop is what keeps a degree away from zero, so `messagePassing`
divides by nothing that can vanish on a nonnegative adjacency. -/
theorem GNN.one_le_degree (A : Mat ℝ N N) (hA : ∀ i j, 0 ≤ A i j) (j : Fin N) :
    1 ≤ GNN.degree A j := by
  -- the identity contributes the self-loop, and the adjacency only adds to it
  have hsplit : GNN.degree A j = (∑ i, A i j) + ∑ i, (1 : Mat ℝ N N) i j := by
    simp only [GNN.degree, Matrix.add_apply, Finset.sum_add_distrib]
  have hone : ∑ i, (1 : Mat ℝ N N) i j = 1 := by
    simp only [Matrix.one_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hnn : 0 ≤ ∑ i, A i j := Finset.sum_nonneg fun i _ => hA i j
  rw [hsplit, hone]
  linarith

/-- `P = D̃^(-1/2) Ã D̃^(-1/2)`, entrywise, `D̃` being diagonal. -/
noncomputable def GNN.messagePassing (A : Mat ℝ N N) : Mat ℝ N N :=
  fun i j => (A + 1) i j / (Real.sqrt (GNN.degree A i) * Real.sqrt (GNN.degree A j))

/-- The layer as one linear map: `W` mixes features, `P` mixes nodes. -/
def GNN.gcnLin (P : Mat ℝ N N) (W : Mat ℝ F₁ F₂) : Mat ℝ N F₁ →ₗ[ℝ] Mat ℝ N F₂ :=
  (matMulLeft P).comp (matMulRight W)

theorem GNN.gcnLin_apply (P : Mat ℝ N N) (W : Mat ℝ F₁ F₂) (H : Mat ℝ N F₁) :
    GNN.gcnLin P W H = P * H * W := by
  show P * (H * W) = P * H * W
  rw [Matrix.mul_assoc]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The layer on a matrix polynomial zonotope, which is the whole of what CORA's
`nnGCNLayer` computes at a graph with no uncertain edges. -/
def GNN.gcn (P : Mat ℝ N N) (W : Mat ℝ F₁ F₂) (PZ : PolyZonotope (Mat ℝ N F₁)) :
    PolyZonotope (Mat ℝ N F₂) := PZ.map (GNN.gcnLin P W)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
