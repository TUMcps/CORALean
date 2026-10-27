module

public import CORALean.ContSet.Zonotope.Float.Zonotope
public import CORALean.ContSet.Interval.Float.Operations.Transpose

@[expose] public section

/-!
# `Zonotope.transpose`, over a floating-point scalar

CORA's `transpose` of a matrix zonotope: the center, every generator and the error box transposed.
Entries are moved, not computed, so nothing rounds.

## Inputs
* `Z` – matrix zonotope

## Output
* matrix zonotope of the transposed matrices
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The center and every generator transposed, the box as well. -/
def Zonotope.transpose (Z : Zonotope (Mat 𝕋 m n)) : Zonotope (Mat 𝕋 n m) where
  h := Z.h
  c := Z.c.transpose
  G := fun k => (Z.G k).transpose
  I_error := Z.I_error.transpose

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
