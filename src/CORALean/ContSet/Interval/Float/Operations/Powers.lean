module

public import CORALean.ContSet.Interval.Float.Operations.MatMul

@[expose] public section

/-!
# `Interval.powers`, over a floating-point scalar

CORA's `powers` of an interval matrix, rounded outward: from the initial power `P`, each next
power multiplies the previous one by `A` from the right, with `Interval.matMul`.

## Inputs
* `A` – interval matrix
* `P` – initial power

## Output
* the power at offset `k` from the initial power
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `P` times `A`, `k` times from the right. -/
def Interval.powers (A P : Interval (Mat 𝕋 n n)) : ℕ → Interval (Mat 𝕋 n n)
  | 0 => P
  | k + 1 => Interval.matMul (Interval.powers A P k) A

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
