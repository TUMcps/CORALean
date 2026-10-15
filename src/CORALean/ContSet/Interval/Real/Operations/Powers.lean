module

public import CORALean.ContSet.Interval.Real.Operations.MatMul

@[expose] public section

/-!
# `Interval.powers`

CORA's `@intervalMatrix/powers`: from the power `pow{initialOrder} = initialPower` the cell array
is `pow{i} = pow{i-1} * intMat`, the interval product on the right. `powers A P k` is the entry
at order `initialOrder + k`; the default call has `P = A` and `initialOrder = 1`, so `powers A A k`
is `pow{k + 1}`. `maxOrder` only cuts the array, and is the caller's bound on `k`.

**Recurses on the right of the accumulated power, `(A ^ k) * A`, unlike `Interval.matPow`**, which
multiplies `A` from the left: the two enclose different sets, since interval products are not
associative.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `pow{initialOrder + k}` of `powers(A, maxOrder, initialOrder, P)`: `P` times `A`, `k` times
from the right. -/
def Interval.powers (A P : Interval (Mat ℝ n n)) : ℕ → Interval (Mat ℝ n n)
  | 0 => P
  | k + 1 => Interval.matMul (Interval.powers A P k) A

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
