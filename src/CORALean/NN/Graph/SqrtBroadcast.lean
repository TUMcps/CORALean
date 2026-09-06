import CORALean.NN.Graph.UncertainSqrt

/-!
# The two matrices of inverse square roots, `s_i` and `s_j`

`D̃^(-1/2) Ã D̃^(-1/2)` is entrywise `Ã_ij ⬝ s_i ⬝ s_j`, so the two normalising
factors enter the product as two full matrices: one constant along rows, one
along columns. `sqrtBroadcast` is both — the entry at `(i,j)` is node `idx i j`'s
inverse square root — and `sqrtRow` and `sqrtCol` are the two index maps, so the
one point computation the enclosure needs is proved once.

Over the same `m + N` factors as `uncertainAdjPad`: `sqrt_affine` supplies the
constant and the edge generators, and the residual the relaxation leaves gets a
factor of its own, node `t`'s generator being nonzero only in node `t`'s row (or
column). Those `N` factors are dependent rather than independent because
`bilin` drops an independent block by construction, so a residual left there
would be silently lost in the product rather than carried through it.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The matrix whose entry `(i,j)` is node `idx i j`'s inverse square root, over
the edge factors and one residual factor per node. -/
noncomputable def GNN.sqrtBroadcast (R : Relaxation invSqrt) (A : Mat ℝ N N)
    (U : Fin m → Fin N × Fin N) (idx : Fin N → Fin N → Fin N) : PolyZonotope (Mat ℝ N N) where
  p := m + N
  h := m + N
  q := 0
  c := fun i j => GNN.sqrtConst R A U (idx i j)
  G := Fin.addCases (fun e => fun i j => GNN.sqrtEdgeCoeff R A U (idx i j) e)
    (fun t => fun i j => if idx i j = t then GNN.sqrtError R A U (idx i j) else 0)
  E := PolyZonotope.identE (m + N)
  GI := Fin.elim0

/-- `s_i` broadcast along each row, the left factor of the normalisation. -/
noncomputable def GNN.sqrtRow (R : Relaxation invSqrt) (A : Mat ℝ N N)
    (U : Fin m → Fin N × Fin N) : PolyZonotope (Mat ℝ N N) :=
  GNN.sqrtBroadcast R A U fun i _ => i

/-- `s_j` broadcast along each column, the right factor of the normalisation. -/
noncomputable def GNN.sqrtCol (R : Relaxation invSqrt) (A : Mat ℝ N N)
    (U : Fin m → Fin N × Fin N) : PolyZonotope (Mat ℝ N N) :=
  GNN.sqrtBroadcast R A U fun _ j => j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
