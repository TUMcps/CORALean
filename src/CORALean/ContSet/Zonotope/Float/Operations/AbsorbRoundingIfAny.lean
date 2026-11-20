module

public import CORALean.ContSet.Zonotope.Float.Operations.AbsorbRounding

@[expose] public section

/-!
# `Zonotope.absorbRoundingIfAny`

The set itself if its error box is zero (`sup ≤ 0 ≤ inf`), else `absorbRounding`. A quadratic map
needs a set without a box; at `nearest` the box is zero and the generators stay as they are.

## Inputs
* `Z` – zonotope

## Output
* zonotope whose error box is zero
-/

-- Authors:       Claude Opus 5.5
-- Written:       20-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.absorbRoundingIfAny (Z : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  if decide (∀ i, le (Z.I_error.sup i) zero = true ∧ le zero (Z.I_error.inf i) = true) then Z
  else Z.absorbRounding

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
