module

public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# `MatExp.factorialUp`, a float upper bound of a factorial

`k! = k · (k-1)!`, one `mulUp` per factor, each factor `k` counted up from `one`
by `nsmulUp`: `k` multiplications rather than the `k!` additions a count of
copies would take, and never below `k!`, both factors being nonnegative upper
bounds, so it is safe to divide by — `Theorems/InvFactorialBoundsFloat` is where
that division happens.
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   25-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def MatExp.factorialUp : ℕ → 𝕋
  | 0 => one
  | k + 1 => mulUp (nsmulUp (k + 1) one) (MatExp.factorialUp k)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
