module

public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

@[expose] public section

/-!
# The terms CORA's `zonotope(pZ)` moves into the center

`zonotopeEven` writes them inline; `zonotopeFold` needs them by name, to add the sum of the terms
to the center instead of the error box. A constant column moves whole, an all-even one by half, the
others not at all.

## Inputs
* `pZ` – polynomial zonotope

## Output
* the shift term of each dependent generator
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `0.5 * Gquad` of the all-even columns, a constant column whole, zero for the others. -/
def PolyZonotope.evenShift (pZ : PolyZonotope (Vec 𝕋 n)) : Fin pZ.h → Vec 𝕋 n := fun l i =>
  if ∀ k, pZ.E k l = 0 then pZ.G l i else if ∀ k, pZ.E k l % 2 = 0 then half (pZ.G l i) else zero

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
