import CORALean.NN.Graph.Operations.DegreeAt

/-!
# The uncertain degree, written affinely in the edge weights

Split out of `UncertainDegreeBounds.lean` (issue #62): the two bounds are read
off this form, and so is the slope the inverse-square-root relaxation is
composed with, so it has users outside the file it grew up in.

The content is one reordering. A degree sums a column of `A(λ) + I`, each entry
of which is a fixed part plus what the weighted edges add; the two separate, and
everything depending on `λ` lands in the second summand, linearly. That
linearity is the whole reason an affine relaxation of `x ↦ x^(-1/2)` composes
with a degree at all.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The degree at `λ` is the fixed one plus what the weighted edges add, which
is the affine form every bound and every relaxation is read off. -/
theorem GNN.degreeAt_eq (A : Mat ℝ N N) (U : Fin m → Fin N × Fin N) (lam : Fin m → ℝ)
    (j : Fin N) :
    GNN.degreeAt A U lam j
      = GNN.degree A j + ∑ e, ∑ i, lam e * GNN.edgeMat (U e) i j := by -- --- PROOF ---
  simp only [GNN.degreeAt, GNN.degree, GNN.adjAt, Matrix.add_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]
  -- the edge contributions separate from the fixed adjacency and the self-loop
  have h : ∀ i : Fin N, A i j + (∑ e, lam e * GNN.edgeMat (U e) i j) + (1 : Mat ℝ N N) i j
      = A i j + (1 : Mat ℝ N N) i j + ∑ e, lam e * GNN.edgeMat (U e) i j := fun i => by ring
  simp only [h]
  rw [Finset.sum_add_distrib, Finset.sum_comm]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
