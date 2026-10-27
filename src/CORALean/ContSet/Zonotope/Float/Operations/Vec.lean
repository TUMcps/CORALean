module

public import CORALean.ContSet.Zonotope.Float.Zonotope
public import CORALean.ContSet.Interval.Float.Operations.Vec

@[expose] public section

/-!
# `Zonotope.vec`, over a floating-point scalar

CORA's `zonotope(matZ)`: the center, every generator and the error box stacked column by column,
entry `(i, j)` going to position `i + m * j`. Entries are moved, not computed, so nothing rounds.

## Inputs
* `Z` – matrix zonotope

## Output
* zonotope of the stacked matrices
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The center and every generator stacked column-major, the box as well. -/
def Zonotope.vec (Z : Zonotope (Mat 𝕋 m n)) : Zonotope (Vec 𝕋 (n * m)) where
  h := Z.h
  c := fun k => Z.c (finProdFinEquiv.symm k).2 (finProdFinEquiv.symm k).1
  G := fun l k => Z.G l (finProdFinEquiv.symm k).2 (finProdFinEquiv.symm k).1
  I_error := Z.I_error.vec

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
