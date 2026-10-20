module

public import CORALean.ContSet.Zonotope.Float.Operations.CubMapGDiff
public import CORALean.ContSet.Zonotope.Float.Operations.CubMapCDown
public import CORALean.ContSet.Zonotope.Float.Operations.CubMapCUp
public import CORALean.ContSet.Zonotope.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `Zonotope.cubMapDep`

CORA's `@zonotope/cubMap` (`aux_cubMapSingle`) at a set whose box is empty, on the stored floats:
the enclosing zonotope of `Real.Zonotope.cubMap`, with center and generators rounded down and what
that leaves to pay in the box (the center's gap to its upper rounding, the generators' gaps, which
a coefficient in `[-1, 1]` spreads either way). Sound only where the operand's own box is empty,
so nothing outside `cubMap` calls it.

## Inputs
* `T` – cubic tensor
* `Z` – zonotope

## Output
* zonotope enclosing the cubic image of a set with empty box
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.cubMapDep (T : Fin m → Fin n → Mat 𝕋 n n) (Z : Zonotope (Vec 𝕋 n)) :
    Zonotope (Vec 𝕋 m) where
  h := (Z.h + 1) * (Z.h + 1) * (Z.h + 1)
  c := Zonotope.cubMapCDown T Z
  G := fun l i => Zonotope.cubMapGDown T Z i l
  I_error := (Interval.residual (Zonotope.cubMapCDown T Z) (Zonotope.cubMapCUp T Z)
    (Zonotope.cubMapCDown T Z)).plus (Zonotope.generatorError (Zonotope.cubMapGDiff T Z))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
