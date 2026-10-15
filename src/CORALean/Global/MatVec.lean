module

public import CORALean.Global.Tensor
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Pi

@[expose] public section

/-!
# `matVecEquiv`

The reshape `reshape(M, [], 1)` and its inverse `reshape(v, [m, n])`, MATLAB's column-major order,
which the matrix-set methods (`zonotope(matZ)`, `polytope(matP)`) use to reuse the vector classes:
entry `(i, j)` of an `m × n` matrix is entry `i + m * j` of the vector. Linear, so it carries sets
across exactly.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The column-major vectorisation: entry `(i, j)` goes to position `i + m * j`. -/
def matVecEquiv : Mat ℝ m n ≃ₗ[ℝ] Vec ℝ (n * m) where
  toFun A := fun k => A (finProdFinEquiv.symm k).2 (finProdFinEquiv.symm k).1
  invFun v := Matrix.of fun i j => v (finProdFinEquiv (j, i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv A := by
    ext i j
    simp
  right_inv v := by
    funext k
    show v (finProdFinEquiv ((finProdFinEquiv.symm k).1, (finProdFinEquiv.symm k).2)) = v k
    rw [Prod.mk.eta, Equiv.apply_symm_apply]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
