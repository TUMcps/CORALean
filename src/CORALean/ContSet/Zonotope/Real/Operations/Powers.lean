module

public import CORALean.ContSet.Zonotope.Real.Operations.MatMul

@[expose] public section

/-!
# `Zonotope.powers`

CORA's `@matZonotope/powers`: from the power `pow{initialOrder} = initialPower` the cell array is
`pow{i} = pow{i-1} * matZ`, the matrix-zonotope product on the right. `powers Z P k` is the entry at
order `initialOrder + k`; the default call has `P = Z` and `initialOrder = 1`, so `powers Z Z k` is
`pow{k + 1}`. `maxOrder` only cuts the array, and is the caller's bound on `k`. Recurses on the
right of the accumulated power, unlike `Zonotope.matPow`, which multiplies on the left: the two
enclose different sets, `matMul` being only an outer product.

## Inputs
* `Z` – base matrix zonotope
* `P` – starting matrix zonotope

## Output
* enclosure of `P` times `Z` repeatedly
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `pow{initialOrder + k}` of `powers(Z, maxOrder, initialOrder, P)`: `P` times `Z`, `k` times
from the right. -/
def Zonotope.powers (Z P : Zonotope (Mat ℝ n n)) : ℕ → Zonotope (Mat ℝ n n)
  | 0 => P
  | k + 1 => Zonotope.matMul (Zonotope.powers Z P k) Z

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
