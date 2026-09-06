import CORALean.ContSet.ContSet.ContSet

/-!
# The subgraph projection, `[1, Cor. 1]`'s `M`

`select κ` is `I_{|𝒩|}(𝒦,·)`: the identity's rows named by the subgraph's node
indices `κ : Fin K → Fin N`. Multiplying it out is what `select_mul` and
`select_mul_transpose` record — `H' = M H`, `P' = M P Mᵀ` — and both are plain
row/column selection, `Matrix.submatrix`, so [1]'s projection costs nothing to
state: it is `select`, and its two products *are* `submatrix`.

Neither theorem needs `κ` injective: `select κ k i` is `1` exactly when
`i = κ k`, so the sum defining each product collapses to that one term whatever
`κ` does, even if it repeats a node or misses one. Injectivity is what
`SubmatrixMulOfClosed` needs instead, once the product is a *restriction of a
larger one* rather than one computed from scratch.

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

variable {N K F : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[1, Cor. 1]`'s `M = I_{|𝒩|}(𝒦,·)`: the rows of the identity the subgraph names. -/
def GNN.select (κ : Fin K → Fin N) : Mat ℝ K N := (1 : Mat ℝ N N).submatrix κ id

theorem GNN.select_mul (κ : Fin K → Fin N) (H : Mat ℝ N F) :
    GNN.select κ * H = H.submatrix κ id := by
  funext k j
  show ∑ i, (1 : Mat ℝ N N) (κ k) i * H i j = H (κ k) j
  simp [Matrix.one_apply]

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
