module

public import CORALean.ContSet.Zonotope.Float.Operations.MatMul
public import CORALean.ContSet.Zonotope.Float.Operations.Basic

@[expose] public section

/-!
# `Zonotope.mpower`, over a floating-point scalar

CORA's `mpower` of a matrix zonotope, rounded outward: the identity for the exponent `0`, the
zonotope itself for `1`, and then `((Z * Z) * Z) * …`, each product `Zonotope.matMul` with the
running power on the left, as CORA's loop multiplies.

## Inputs
* `Z` – matrix zonotope

## Output
* matrix zonotope enclosing the `k`-th power of its members
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

/-- The identity, `Z`, then the running power times `Z` from the right. -/
def Zonotope.mpower (Z : Zonotope (Mat 𝕋 n n)) : ℕ → Zonotope (Mat 𝕋 n n)
  | 0 => Zonotope.pointMat (diagonalBlock fun _ => one)
  | 1 => Z
  | k + 2 => Zonotope.matMul (Zonotope.mpower Z (k + 1)) Z

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
