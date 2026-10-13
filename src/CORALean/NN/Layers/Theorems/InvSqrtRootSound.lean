import CORALean.NN.Layers.Operations.InvSqrtRoot
import CORALean.NN.Layers.Theorems.ActivationSound
import CORALean.NN.Layers.Theorems.InvSqrtRootRelaxationSound

/-!
# What the inverse square root layer encloses

`Real.invSqrt` coordinatewise, for every point of every set.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.invSqrtRoot_sound (p : ℕ) :
    (Layer.invSqrtRoot (𝕋 := 𝕋) (S := S) (n := n) p).Sound fun x i => Real.invSqrt (x i) :=
  Layer.activation_sound (invSqrtRootRelaxation_sound p)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
