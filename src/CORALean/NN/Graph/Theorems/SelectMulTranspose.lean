import CORALean.NN.Graph.Theorems.SelectMul

/-!
# `select` multiplies out to row-and-column selection

Neither this nor `select_mul` needs `κ` injective: `select κ k i` is `1`
exactly when `i = κ k`, so the sum defining each product collapses to that one
term whatever `κ` does, even if it repeats a node or misses one. Injectivity is
what `SubmatrixMulOfClosed` needs instead, once the product is a *restriction
of a larger one* rather than one computed from scratch.
-/

-- Authors:       Claude Sonnet 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N K : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `H' = M H` restricts rows; `P' = M P Mᵀ` restricts rows and columns together, the
subgraph's own message-passing matrix. -/
theorem GNN.select_mul_transpose (κ : Fin K → Fin N) (P : Mat ℝ N N) :
    GNN.select κ * P * (GNN.select κ)ᵀ = P.submatrix κ κ := by -- --- PROOF ---
  -- the row selection collapses first, exactly as `select_mul` says
  rw [GNN.select_mul]
  -- what is left is a column selection, read off `select_mul` through a transpose
  have hcol : P.submatrix κ id * (GNN.select κ)ᵀ = (P.submatrix κ id).submatrix id κ := by
    have h := congrArg Matrix.transpose (GNN.select_mul κ (P.submatrix κ id)ᵀ)
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_submatrix]
      using h
  rw [hcol, Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
