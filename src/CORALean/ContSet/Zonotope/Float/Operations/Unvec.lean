module

public import CORALean.ContSet.Zonotope.Float.Zonotope
public import CORALean.ContSet.Interval.Float.Operations.Unvec

@[expose] public section

/-!
# `Zonotope.unvec`, over a floating-point scalar

The inverse of `Zonotope.vec`: the center, every generator and the error box of a zonotope of
stacked matrices reshaped back into matrices, position `i + m * j` going to entry `(i, j)`. Entries
are moved, not computed, so nothing rounds.

## Inputs
* `Z` – zonotope of stacked matrices

## Output
* matrix zonotope of the unstacked center and generators
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The center, each generator and the box unstacked. -/
def Zonotope.unvec (Z : Zonotope (Vec 𝕋 (n * m))) : Zonotope (Mat 𝕋 m n) where
  h := Z.h
  c := fun i j => Z.c (finProdFinEquiv (j, i))
  G := fun l i j => Z.G l (finProdFinEquiv (j, i))
  I_error := Z.I_error.unvec

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
