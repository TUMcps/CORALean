module

public import CORALean.ContSet.Taylm.Float.Taylm

@[expose] public section

/-!
# `Taylm.InBox`, over a floating-point scalar

A real point lies in the box whose stored float ends are read as reals.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.InBox (B : Fin n → 𝕋 × 𝕋) (t : Vec ℝ n) : Prop :=
  ∀ k, toReal (B k).1 ≤ t k ∧ t k ≤ toReal (B k).2

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
