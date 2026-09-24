import CORALean.NN.Layers.Operations.Sigmoid
import CORALean.NN.Layers.Theorems.ActivationSound
import CORALean.NN.Layers.Theorems.SigmoidRelaxationSound

/-!
# What the sigmoid layer encloses

`Real.sigmoid` coordinatewise, at every reduction depth.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.sigmoid_sound (k : ℕ) :
    (Layer.sigmoid (𝕋 := 𝕋) (S := S) (n := n) k).Sound fun x i => Real.sigmoid (x i) :=
  Layer.activation_sound (sigmoidRelaxation_sound k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
