module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Bilin
public import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE
public import CORALean.Global.Hadamard
public import CORALean.NN.Graph.Operations.Degree
public import CORALean.NN.Graph.Operations.DegreeSup
public import CORALean.NN.Graph.Operations.EdgeMat
public import CORALean.NN.Graph.Operations.SqrtConst
public import CORALean.NN.Graph.Operations.SqrtEdgeCoeff
public import CORALean.NN.Layers.Definitions.Enclosure
public import CORALean.NN.Layers.Definitions.InvSqrt
public import CORALean.NN.Layers.Definitions.InvSqrtRelaxation
public import CORALean.NN.Layers.Definitions.Relaxation
public import CORALean.NN.Layers.Definitions.ScaleRounding
public import CORALean.NN.Layers.Operations.LayerRelaxationBox
public import CORALean.NN.Layers.Operations.RelaxationBox

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
variable {N m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- How far the affine map may miss `invSqrt` over that interval. -/
noncomputable def GNN.aux_sqrtError (R : Relaxation ℝ) (A : Mat ℝ N N)
    (U : Fin m → Fin N × Fin N) (j : Fin N) : ℝ :=
  R.error (GNN.degree A j) (GNN.degreeSup A U j)

/-- The matrix whose entry `(i,j)` is node `idx i j`'s inverse square root, over
the edge factors and one residual factor per node. -/
noncomputable def GNN.aux_sqrtBroadcast (R : Relaxation ℝ) (A : Mat ℝ N N)
    (U : Fin m → Fin N × Fin N) (idx : Fin N → Fin N → Fin N) : PolyZonotope (Mat ℝ N N) where
  p := m + N
  h := m + N
  q := 0
  c := fun i j => GNN.sqrtConst R A U (idx i j)
  G := Fin.addCases (fun e => fun i j => GNN.sqrtEdgeCoeff R A U (idx i j) e)
    (fun t => fun i j => if idx i j = t then GNN.aux_sqrtError R A U (idx i j) else 0)
  E := PolyZonotope.identE (m + N)
  GI := Fin.elim0

/-- `s_j` broadcast along each column, the right factor of the normalisation. -/
noncomputable def GNN.aux_sqrtCol (R : Relaxation ℝ) (A : Mat ℝ N N)
    (U : Fin m → Fin N × Fin N) : PolyZonotope (Mat ℝ N N) :=
  GNN.aux_sqrtBroadcast R A U fun _ j => j

/-- `s_i` broadcast along each row, the left factor of the normalisation. -/
noncomputable def GNN.aux_sqrtRow (R : Relaxation ℝ) (A : Mat ℝ N N)
    (U : Fin m → Fin N × Fin N) : PolyZonotope (Mat ℝ N N) :=
  GNN.aux_sqrtBroadcast R A U fun i _ => i

/-- `Ã = A(λ) + I` as a matrix polynomial zonotope over `m + N` factors, the
last `N` of which it leaves to the inverse square roots. -/
noncomputable def GNN.aux_uncertainAdjPad (A : Mat ℝ N N) (U : Fin m → Fin N × Fin N) :
    PolyZonotope (Mat ℝ N N) where
  p := m + N
  h := m + N
  q := 0
  c := A + 1 + ∑ e, (1/2 : ℝ) • GNN.edgeMat (U e)
  G := Fin.addCases (fun e => (1/2 : ℝ) • GNN.edgeMat (U e)) (fun _ => 0)
  E := PolyZonotope.identE (m + N)
  GI := Fin.elim0


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1]'s `𝒫`: the padded adjacency paired entrywise with the row and the column
of inverse square roots, over one shared set of factors. -/
noncomputable def GNN.messagePassingEnclosure {N m : ℕ} (R : Relaxation ℝ)
    (A : Mat ℝ N N) (U : Fin m → Fin N × Fin N) : PolyZonotope (Mat ℝ N N) :=
  ((GNN.aux_uncertainAdjPad A U).bilin Entrywise.hadamardLin (GNN.aux_sqrtRow R A U) rfl).bilin
    Entrywise.hadamardLin (GNN.aux_sqrtCol R A U) rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
