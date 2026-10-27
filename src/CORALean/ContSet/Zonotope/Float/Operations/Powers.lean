module

public import CORALean.ContSet.Zonotope.Float.Operations.MatMul

@[expose] public section

/-!
# `Zonotope.powers`, over a floating-point scalar

CORA's `powers` of a matrix zonotope, rounded outward: from the initial power `P`, each next power
multiplies the previous one by `Z` from the right, with `Zonotope.matMul`.

## Inputs
* `Z` – matrix zonotope
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

/-- `P` times `Z`, `k` times from the right. -/
def Zonotope.powers (Z P : Zonotope (Mat 𝕋 n n)) : ℕ → Zonotope (Mat 𝕋 n n)
  | 0 => P
  | k + 1 => Zonotope.matMul (Zonotope.powers Z P k) Z

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
