import CORALean.ContSet.ConPolyZono.Real.ConPolyZono

/-!
# `ConPolyZono.padE`

An exponent matrix widened by fresh factors that none of its monomials uses:
what a constraint block keeps when an operation adds factors beside the ones it
was written against.

-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Real

def ConPolyZono.padE {p s : ℕ} (EC : Fin p → Fin s → ℕ) (r : ℕ) :
    Fin (p + r) → Fin s → ℕ :=
  Fin.append EC fun _ _ => 0

end CORALean.Real
