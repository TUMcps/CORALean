import CORALean.ContSet.ConPolyZono.Real.ConPolyZono
import CORALean.ContSet.PolyZonotope.Real.Operations.PadE

/-!
# `ConPolyZono.padE`

An exponent matrix widened by fresh factors that none of its monomials uses:
what a constraint block keeps when an operation adds factors beside the ones it
was written against.

`PolyZonotope.padE` read at a constraint's exponent matrix rather than at a
generator block, and the same function: a constraint and a generator are two
readings of one factor vector, so widening that vector is one operation. The
name is kept because a caller reaching for it here is padding constraints.
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.padE {p s : ℕ} (EC : Fin p → Fin s → ℕ) (r : ℕ) :
    Fin (p + r) → Fin s → ℕ :=
  PolyZonotope.padE EC r

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
