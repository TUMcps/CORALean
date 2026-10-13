module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Bilin
public import CORALean.Global.Hadamard
public import CORALean.NN.Graph.Operations.SqrtCol
public import CORALean.NN.Graph.Operations.SqrtRow
public import CORALean.NN.Graph.Operations.UncertainAdjPad

@[expose] public section

/-!
# The message-passing enclosure `𝒫 ⊇ D̃^(-1/2) Ã D̃^(-1/2)`

[1, Prop. 4]'s message passing at an uncertain structure, as one matrix polynomial
zonotope: `P_ij = Ã_ij ⬝ s_i ⬝ s_j` is two entrywise products, so it is
`PolyZonotope.bilin` at `Entrywise.hadamardLin`, twice.

`Mat ℝ N N` needs `hadamardLin` and not `*`, its own multiplication being the
matrix product; that is what `Global/Hadamard` exists for.

All three sets are written over the same `m + N` factors — `m` edges, `N`
residuals — so both sharing hypotheses are `rfl`, and `bilin` keeps `S₁.p`, so
the second one is `rfl` too. Sharing is the point: an edge appears in `Ã` and
in both degrees, and a product over unshared factors would count it three
times.

An enclosure and not an equality: the inverse square root is not affine, so the
residual factors buy soundness rather than exactness.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Claude Sonnet 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1]'s `𝒫`: the padded adjacency paired entrywise with the row and the column
of inverse square roots, over one shared set of factors. -/
noncomputable def GNN.messagePassingEnclosure {N m : ℕ} (R : Relaxation ℝ)
    (A : Mat ℝ N N) (U : Fin m → Fin N × Fin N) : PolyZonotope (Mat ℝ N N) :=
  ((GNN.uncertainAdjPad A U).bilin Entrywise.hadamardLin (GNN.sqrtRow R A U) rfl).bilin
    Entrywise.hadamardLin (GNN.sqrtCol R A U) rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
