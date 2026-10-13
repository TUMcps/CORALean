module

public import CORALean.ContSet.Capsule.Float.Capsule

@[expose] public section

/-!
# `Capsule.origin` over a floating-point scalar

No direction, no radius, centred at the origin: `zero` reads as `0`, so nothing rounds.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Capsule.origin (n : ℕ) : Capsule 𝕋 n := ⟨fun _ => zero, fun _ => zero, zero⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
