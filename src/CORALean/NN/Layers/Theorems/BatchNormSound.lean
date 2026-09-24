import CORALean.NN.Layers.Operations.BatchNorm
import CORALean.NN.Layers.Theorems.LinearSound

/-!
# What the batch normalization layer encloses

The affine map the stored scale and shift denote, coordinate by coordinate: the diagonal the
layer places reads back as `Matrix.diagonal` of the scales, `toReal_diagonalBlock`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Float Float.SoundFloatArithmetic

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.OfInterval S 𝕋] {n c : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.batchNorm_sound (chan : Fin n → Fin c) (scale shift : Vec 𝕋 c) :
    (Layer.batchNorm (S := S) chan scale shift).Sound
      fun x i => toReal (scale (chan i)) * x i + toReal (shift (chan i)) := by -- --- PROOF ---
  refine (Layer.linear_sound _ _).congr fun x => funext fun i => ?_
  -- the placed diagonal reads back as the diagonal of the scales
  have hdiag : toRealMat (diagonalBlock fun i => scale (chan i))
      = Matrix.diagonal (toRealVec fun i => scale (chan i)) := by
    funext p q
    exact toReal_diagonalBlock _ p q
  show toReal (scale (chan i)) * x i + toReal (shift (chan i))
    = (toRealMat (diagonalBlock fun i => scale (chan i)) *ᵥ x) i
      + toRealVec (fun i => shift (chan i)) i
  rw [hdiag, Matrix.mulVec_diagonal]
  rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
