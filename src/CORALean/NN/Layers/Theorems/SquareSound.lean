import CORALean.NN.Layers.Operations.Square
import CORALean.NN.Layers.Theorems.ActivationSound
import CORALean.NN.Layers.Theorems.SquareRelaxationSound

/-!
# What the square layer encloses

`x ↦ x²` coordinatewise.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Float.SoundFloatArithmetic

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.square_sound :
    (Layer.square (𝕋 := 𝕋) (S := S) (n := n)).Sound fun x i => x i ^ 2 :=
  Layer.activation_sound (σ := fun x : ℝ => x ^ 2) squareRelaxation_sound

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
