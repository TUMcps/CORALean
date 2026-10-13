module

public import CORALean.Global.Float.Instances.Flint.Flint

@[expose] public section

/-!
# Negation

Exact and pure Lean: the sign of the mantissa flips and nothing is rounded, so
FLINT is not asked.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace Flint

variable {p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def neg (a : Flint p) : Flint p := ⟨-a.mantissa, a.exponent⟩

end Flint

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
