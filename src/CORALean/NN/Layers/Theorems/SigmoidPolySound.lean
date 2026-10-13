module

public import CORALean.NN.Layers.Operations.SigmoidPoly
public import CORALean.NN.Layers.Theorems.ActivationPolySound
public import CORALean.NN.Layers.Theorems.SigmoidPolyRelaxationSound

@[expose] public section

/-!
# What the polynomial sigmoid layer encloses

`Real.sigmoid` coordinatewise, which the layer itself never mentions.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ} {N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.sigmoidPoly_sound (k : ℕ) (c : Fin n → 𝕋 → 𝕋 → Fin (m + 1) → 𝕋)
    (dx : Fin n → 𝕋 → 𝕋 → 𝕋) (p : Fin n → 𝕋 → 𝕋 → Fin (N + 1) → 𝕋) :
    (Layer.sigmoidPoly k c dx p).Sound fun x i => Real.sigmoid (x i) :=
  Layer.activationPoly_sound fun i => sigmoidPolyRelaxation_sound k (c i) (dx i) (p i)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
