import CORALean.NN.Layers.Operations.Tanh
import CORALean.NN.Layers.Theorems.ActivationSound
import CORALean.NN.Layers.Theorems.TanhRelaxationSound

/-!
# What the tanh layer encloses

`Real.tanh` coordinatewise, at every reduction depth.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.tanh_sound (k : ℕ) :
    (Layer.tanh (𝕋 := 𝕋) (S := S) (n := n) k).Sound fun x i => Real.tanh (x i) :=
  Layer.activation_sound (tanhRelaxation_sound k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
