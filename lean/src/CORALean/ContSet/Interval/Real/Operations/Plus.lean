import CORALean.ContSet.Interval.Real.Interval

/-!
# `Interval.plus`

CORA's `@interval/plus`: bounds add coordinatewise.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

def Interval.plus (I₁ I₂ : Interval n) : Interval n where
  inf := I₁.inf + I₂.inf
  sup := I₁.sup + I₂.sup

end CORALean.Real
