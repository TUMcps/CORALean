module

public import CORALean.NN.Graph.Operations.EdgeMat
public import CORALean.NN.Graph.Operations.MatMulBilin
public import CORALean.NN.Graph.Theorems.SelectMatToReal
public import CORALean.NN.Graph.Theorems.SelectMul

@[expose] public section

/-!
# `NN/Graph/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real

open Matrix

variable {N F₁ F₂ : ℕ}


-- ===================================  `GNN.edgeMat_nonneg`  =================================== --
-- Authors:       Claude Sonnet 5
-- Written:       06-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---

/-- An edge only ever adds to a degree, which is what bounds an uncertain one. -/
theorem GNN.edgeMat_nonneg (ij : Fin N × Fin N) (a b : Fin N) : 0 ≤ GNN.edgeMat ij a b := by
  simp only [GNN.edgeMat]
  split_ifs
  exacts [zero_le_one, le_refl 0]


-- =================================  `GNN.matMulBilin_apply`  ================================== --
-- Authors:       Claude Sonnet 5
-- Written:       06-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---

/-- The bundling adds nothing to read back: applying the bilinear map is `rfl`. -/
@[simp] theorem GNN.matMulBilin_apply (X : Mat ℝ N F₁) (Y : Mat ℝ F₁ F₂) :
    GNN.matMulBilin N F₁ F₂ X Y = X * Y := rfl

end CORALean.Real


namespace CORALean

open Matrix Scalar

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {N K F : ℕ}


-- ===================================  `GNN.selectMat_mul`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Row selection at any scalar: the stored matrix times the stored features, read as reals, is
`Matrix.submatrix`. -/
theorem GNN.selectMat_mul (κ : Fin K → Fin N) (H : Mat 𝕋 N F) :
    toRealMat (GNN.selectMat 𝕋 κ) * toRealMat H = (toRealMat H).submatrix κ id := by
  rw [GNN.selectMat_toReal, Real.GNN.select_mul]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
