import CORALean.Global.Float.Instances.Flint.Flint

/-!
# Negation

Exact and pure Lean: the sign of the mantissa flips and nothing is rounded, so
FLINT is not asked.
-/

-- Authors:       Tobias Ladner
-- Written:       28-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace Flint

variable {p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def neg (a : Flint p) : Flint p := ⟨-a.mantissa, a.exponent⟩

end Flint

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
