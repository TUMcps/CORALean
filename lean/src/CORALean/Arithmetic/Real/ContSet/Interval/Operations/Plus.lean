import CORALean.Arithmetic.Real.ContSet.Interval.Interval

/-!
# `Interval.plus`

CORA's `@interval/plus`: bounds add coordinatewise.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Real

variable {n : ℕ}

def Interval.plus (I₁ I₂ : Interval n) : Interval n where
  inf := I₁.inf + I₂.inf
  sup := I₁.sup + I₂.sup

end CORALean.Arithmetic.Real
