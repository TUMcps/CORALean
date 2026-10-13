module

public import CORALean.ContSet.Capsule.Float.Capsule

@[expose] public section

/-!
# `Capsule.empty` over a floating-point scalar

Radius `-1`, as over ℝ: `neg one` reads as `-1`, which no point is within.
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

def Capsule.empty (n : ℕ) : Capsule 𝕋 n := ⟨fun _ => zero, fun _ => zero, neg one⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
