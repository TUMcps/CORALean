module

public import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE
public import CORALean.NN.Graph.Operations.SqrtConst
public import CORALean.NN.Graph.Operations.SqrtEdgeCoeff
public import CORALean.NN.Graph.Operations.SqrtError

@[expose] public section

/-!
# The matrix of inverse square roots, broadcast along an index

`D̃^(-1/2) Ã D̃^(-1/2)` is entrywise `Ã_ij ⬝ s_i ⬝ s_j`, so the two normalising
factors enter the product as two full matrices. `sqrtBroadcast` is both — the
entry at `(i,j)` is node `idx i j`'s inverse square root — and `sqrtRow` and
`sqrtCol` are the two index maps, so the one point computation the enclosure
needs is proved once.

Over `m + N` factors, `m` edges and `N` residuals: `sqrt_affine` supplies the
constant and the edge generators, and the residual the relaxation leaves gets a
factor of its own, node `t`'s generator being nonzero only in node `t`'s row (or
column). Those `N` factors are dependent rather than independent because
`bilin` drops an independent block by construction, so a residual left there
would be silently lost in the product rather than carried through it.
-/

-- Authors:       Claude Sonnet 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {N m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The matrix whose entry `(i,j)` is node `idx i j`'s inverse square root, over
the edge factors and one residual factor per node. -/
noncomputable def GNN.sqrtBroadcast (R : Relaxation ℝ) (A : Mat ℝ N N)
    (U : Fin m → Fin N × Fin N) (idx : Fin N → Fin N → Fin N) : PolyZonotope (Mat ℝ N N) where
  p := m + N
  h := m + N
  q := 0
  c := fun i j => GNN.sqrtConst R A U (idx i j)
  G := Fin.addCases (fun e => fun i j => GNN.sqrtEdgeCoeff R A U (idx i j) e)
    (fun t => fun i j => if idx i j = t then GNN.sqrtError R A U (idx i j) else 0)
  E := PolyZonotope.identE (m + N)
  GI := Fin.elim0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
