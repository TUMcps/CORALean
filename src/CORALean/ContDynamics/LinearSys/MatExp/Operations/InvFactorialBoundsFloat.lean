module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.FactorialDownFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.FactorialUpFloat
public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `MatExp.invFactorialBounds`, a float enclosure of `1 / k!`

`1/k!` is irrational in binary, so `expIntervalTaylor`'s coefficient needs both
directions: divide `one` by the factorial's upper bound to round down, by its
lower bound (held positive) to round up. Returned as an interval, one declaration
covering both bounds rather than two files that would otherwise duplicate the
factorial computation.
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The interval `[lo, hi]` with `lo ≤ 1/k! ≤ hi`. -/
def MatExp.invFactorialBounds (k : ℕ) : Interval 𝕋 :=
  ⟨divDown one (MatExp.factorialUp k), divUp one (MatExp.factorialDown k)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
