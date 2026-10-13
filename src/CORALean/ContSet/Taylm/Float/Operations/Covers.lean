import CORALean.ContSet.Taylm.Float.Operations.InBox

/-!
# `Taylm.Covers`, over a floating-point scalar

Every point of the box `X` lies in one of the boxes `l`.
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

def Taylm.Covers (X : Fin n → 𝕋 × 𝕋) (l : List (Fin n → 𝕋 × 𝕋)) : Prop :=
  ∀ t, Taylm.InBox X t → ∃ B ∈ l, Taylm.InBox B t

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
