module

public import Mathlib.Algebra.Order.Field.Rat

@[expose] public section

/-!
# The step count a horizon and a time step determine

CORA's `steps = (tFinal - tStart) / timeStep`, taken in ℚ where it is exact, and
kept only if it is a natural number — the check CORA's `validateOptions` makes to
a tolerance of `1e-9` (`change_intsteps`), here made exactly — and only for a
positive `timeStep`, CORA's `gezero` check. `none` otherwise, no rounding. A float
algorithm reaches ℚ from its scalar through `ToRat`, which reads a NaN `timeStep` as
`1.5 · 2 ^ 1024`: a count `≥ 1` then needs `tFinal - tStart` to be a multiple of that, and any
step run with the NaN returns a NaN, which the `…Checked` entry points reject.
-/

-- Authors:       Claude Opus 5.5
-- Written:       30-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `(tFinal - tStart) / timeStep` if `timeStep > 0` and the quotient is a natural
number, `none` otherwise. -/
def Reach.steps (tStart tFinal timeStep : ℚ) : Option ℕ :=
  let q := (tFinal - tStart) / timeStep                            -- steps, exactly
  if 0 < timeStep ∧ q.den = 1 ∧ 0 ≤ q then some q.num.toNat else none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
