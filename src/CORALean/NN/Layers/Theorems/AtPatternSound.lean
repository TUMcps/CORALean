import CORALean.NN.Layers.Operations.PolyRelaxationFamilyAtPattern
import CORALean.NN.Layers.Theorems.DegLeDegOf
import CORALean.NN.Layers.Theorems.PadToSound

/-!
# A sound family is sound at every pattern

Padding is where each neuron's own degree bound is spent, and it is the only thing the common
degree costs.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ} {σ : ℝ → ℝ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyRelaxationFamily.atPattern_sound {F : PolyRelaxationFamily 𝕋} (hF : F.Sound σ)
    (t : OrderPattern n) (i : Fin n) : (F.atPattern t i).Sound σ :=
  PolyRelaxation.padTo_sound (F.deg_le_degOf t i) (hF.rel_sound (t i))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
