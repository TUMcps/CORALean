module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.FactorialDownFloat
public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `MatExp.invFactorialBounds`, a float enclosure of `1 / k!`

`1/k!` is irrational in binary, so `expIntervalTaylor`'s coefficient needs both
directions: divide `one` by the factorial's upper bound to round down, by its
lower bound (held positive) to round up. Returned as an interval, one declaration
covering both bounds rather than two files that would otherwise duplicate the
factorial computation.

## Inputs
* `k` – factorial argument

## Output
* float interval enclosing the inverse factorial
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

def MatExp.aux_factorialUp : ℕ → 𝕋
  | 0 => one
  | k + 1 => mulUp (nsmulUp (k + 1) one) (MatExp.aux_factorialUp k)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The interval `[lo, hi]` with `lo ≤ 1/k! ≤ hi`. -/
def MatExp.invFactorialBounds (k : ℕ) : Interval 𝕋 :=
  ⟨divDown one (MatExp.aux_factorialUp k), divUp one (MatExp.factorialDown k)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
