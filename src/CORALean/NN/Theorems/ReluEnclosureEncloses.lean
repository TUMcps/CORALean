module

public import CORALean.NN.Operations.ReluEnclosure
public import CORALean.NN.Definitions.ScalarEncloses

@[expose] public section

/-!
# `reluEnclosure` encloses ReLU
Monotonicity of `max 0`, and `maximum` reads as `max`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem reluEnclosure_encloses : ScalarEncloses (reluEnclosure (𝕋 := 𝕋)) (fun x => max 0 x) :=
  fun _ _ hl hu => by
    simp only [reluEnclosure, toReal_maximum, toReal_zero]
    exact ⟨max_le_max le_rfl hl, max_le_max le_rfl hu⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
