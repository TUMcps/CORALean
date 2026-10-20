module

public import CORALean.NN.Layers.Operations.Basic
public import CORALean.NN.Layers.Operations.Relu
public import CORALean.NN.Layers.Theorems.ActivationEncloses
public import CORALean.NN.Layers.Theorems.ReluRelaxationSound

@[expose] public section

/-!
# What the ReLU layer encloses

ReLU coordinatewise, at every slope: `reluRelaxation_sound` read through the activation
layer's own soundness.

## Inputs
* `lam` – slope choice for each box

## Hypotheses
* none

## Conclusion
* the layer encloses ReLU coordinatewise
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.relu_encloses (lam : 𝕋 → 𝕋 → 𝕋) :
    (Layer.relu (S := S) (n := n) lam).Encloses fun x i => Real.relu (x i) :=
  Layer.activation_encloses (reluRelaxation_sound lam)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
