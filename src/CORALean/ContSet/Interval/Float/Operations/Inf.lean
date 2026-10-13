module

public import CORALean.ContSet.Interval.Float.Operations.EBox

@[expose] public section

/-!
# `Interval.Inf`, over a floating-point scalar

CORA's `interval.Inf(n)`: `(-∞, ∞)ⁿ`, no bound stored in any coordinate.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.Inf (n : ℕ) : Interval.EBox 𝕋 n := ⟨fun _ => none, fun _ => none⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
