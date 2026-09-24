import CORALean.NN.Graph.Operations.DegreeAt
import CORALean.NN.Graph.Operations.SqrtConst
import CORALean.NN.Graph.Operations.SqrtEdgeCoeff
import CORALean.NN.Graph.Theorems.DegreeAtEq

/-!
# `D̃^(-1/2)` at an uncertain degree, as an affine function of the edge factors

The inverse square root of node `j`'s degree, read through a `Relaxation` at the
box `[degreeInf, degreeSup]` that node's degree is known to sit in. What comes
back is a slope, an offset and an error, and composing the slope with the affine
`degreeAt` of `degreeAt_eq` leaves `s_j` affine in the edge weights again:

    s_j = sqrtConst + Σₑ sqrtEdgeCoeff ⬝ αₑ + (residual, at most sqrtError)

`sqrt_affine` is that identity, stated at the factors `α = 2λ - 1` the uncertain
adjacency already uses, so the two sets share their factors and a product of
them keeps the dependence. The residual is not here: it is a factor of its own,
one per node, and only the enclosure that spends it knows how many nodes there
are to spend it on.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {N m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The relaxation's affine map at an uncertain degree, rewritten over the edge
factors `α = 2λ - 1` the uncertain adjacency is built on. -/
theorem GNN.sqrt_affine (R : Relaxation ℝ) (A : Mat ℝ N N) (U : Fin m → Fin N × Fin N)
    (lam : Fin m → ℝ) (j : Fin N) :
    GNN.sqrtSlope R A U j * GNN.degreeAt A U lam j + GNN.sqrtOffset R A U j
      = GNN.sqrtConst R A U j
        + ∑ e, GNN.sqrtEdgeCoeff R A U j e * (2 * lam e - 1) := by -- --- PROOF ---
  -- an edge's contribution to the degree is its weight times its column sum
  have hc : ∀ e, ∑ i, lam e * GNN.edgeMat (U e) i j = lam e * GNN.degreeCoeff U e j :=
    fun e => (Finset.mul_sum _ _ _).symm
  -- split into the half the centre carries and the half the factor scales
  have hsum : ∑ e, GNN.sqrtSlope R A U j * (lam e * GNN.degreeCoeff U e j)
      = GNN.sqrtSlope R A U j * ∑ e, GNN.degreeCoeff U e j / 2
        + ∑ e, GNN.sqrtEdgeCoeff R A U j e * (2 * lam e - 1) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun e _ => by rw [GNN.sqrtEdgeCoeff]; ring
  have hL : GNN.sqrtSlope R A U j * ∑ e, lam e * GNN.degreeCoeff U e j
      = ∑ e, GNN.sqrtSlope R A U j * (lam e * GNN.degreeCoeff U e j) := Finset.mul_sum _ _ _
  rw [GNN.degreeAt_eq, GNN.sqrtConst]
  simp only [hc]
  rw [mul_add, hL, hsum, mul_add]
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
