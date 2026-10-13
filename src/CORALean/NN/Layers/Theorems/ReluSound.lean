import CORALean.NN.Layers.Operations.Relu
import CORALean.NN.Layers.Theorems.ActivationSound
import CORALean.NN.Layers.Theorems.ReluRelaxationSound

/-!
# What the ReLU layer encloses

ReLU coordinatewise, at every slope: `reluRelaxation_sound` read through the activation
layer's own soundness.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.relu_sound (lam : 𝕋 → 𝕋 → 𝕋) :
    (Layer.relu (S := S) (n := n) lam).Sound fun x i => Real.relu (x i) :=
  Layer.activation_sound (reluRelaxation_sound lam)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
