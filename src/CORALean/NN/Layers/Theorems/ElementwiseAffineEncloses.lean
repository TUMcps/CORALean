module

public import CORALean.NN.Layers.Definitions.Basic
public import CORALean.NN.Layers.Operations.ElementwiseAffine
public import CORALean.NN.Layers.Theorems.Basic
public import CORALean.NN.Layers.Theorems.LinearEncloses

@[expose] public section

/-!
# What the elementwise affine layer encloses

The affine map the stored scale and offset denote, coordinate by coordinate: the diagonal the
layer places reads back as `Matrix.diagonal` of the scales, `toReal_diagonalBlock`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Float Float.SoundFloatArithmetic

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.OfInterval S 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.elementwiseAffine_encloses (scale offset : Vec 𝕋 n) :
    (Layer.elementwiseAffine (S := S) scale offset).Encloses
      fun x i => toReal (scale i) * x i + toReal (offset i) := by -- --- PROOF ---
  refine (Layer.linear_encloses _ _).congr fun x => funext fun i => ?_
  have hdiag : toRealMat (diagonalBlock scale) = Matrix.diagonal (toRealVec scale) := by
    funext p q
    exact toReal_diagonalBlock _ p q
  show toReal (scale i) * x i + toReal (offset i)
    = (toRealMat (diagonalBlock scale) *ᵥ x + toRealVec offset) i
  rw [hdiag, Pi.add_apply, Matrix.mulVec_diagonal]
  rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
