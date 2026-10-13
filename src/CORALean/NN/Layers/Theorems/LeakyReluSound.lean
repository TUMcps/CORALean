module

public import CORALean.NN.Layers.Operations.LeakyRelu
public import CORALean.NN.Layers.Theorems.ActivationSound
public import CORALean.NN.Layers.Theorems.LeakyReluRelaxationSound

@[expose] public section

/-!
# What the leaky ReLU layer encloses

`Real.leakyRelu` at the stored `α`, coordinatewise, at every slope, for `α ≤ 1`.
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

theorem Layer.leakyRelu_sound (α : 𝕋) (hα : toReal α ≤ 1) (lam : 𝕋 → 𝕋 → 𝕋) :
    (Layer.leakyRelu (S := S) (n := n) α lam).Sound fun x i => Real.leakyRelu (toReal α) (x i) :=
  Layer.activation_sound (leakyReluRelaxation_sound α hα lam)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
