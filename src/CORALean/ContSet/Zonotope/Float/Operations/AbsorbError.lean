module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Zonotope.Float.Operations.Basic
public import CORALean.ContSet.Zonotope.Float.Operations.ShiftDown

@[expose] public section

/-!
# `Zonotope.absorbError`

Trade the box for `n` generators about its own midpoint. Over ℝ this moves
nothing; here the shifted center must be stored as a float, so the box is left
holding what that rounding still owes rather than becoming `[0, 0]`.

`shiftDown`, `shiftUp` and `errorRadius` are shared with `reduceAndAbsorbBy`,
which does this and a reduction in one pass.

## Inputs
* `Z` – zonotope

## Output
* zonotope with the box traded for generators about its midpoint
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.absorbError (Z : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) where
  h := Z.h + n
  c := Z.shiftDown
  G := Fin.append Z.G (diagonalBlock Z.errorRadius)
  I_error := Interval.residual Z.shiftDown Z.shiftUp Z.shiftDown

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
