module

public import CORALean.ContSet.Zonotope.Float.Operations.CubMapGDown
public import CORALean.ContSet.Zonotope.Float.Operations.CubMapGUp

@[expose] public section

/-!
# `Zonotope.cubMapGDiff`

How far a stored generator of `Zonotope.cubMap` can be from the exact one: the gap between its two
roundings, which a coefficient in `[-1, 1]` then spreads either way.

## Inputs
* `T` – cubic tensor
* `Z` – zonotope

## Output
* gap between the two roundings of each generator
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.cubMapGDiff (T : Fin m → Fin n → Mat 𝕋 n n) (Z : Zonotope (Vec 𝕋 n)) :
    Fin m → Fin ((Z.h + 1) * (Z.h + 1) * (Z.h + 1)) → 𝕋 :=
  fun i l => subUp (Zonotope.cubMapGUp T Z i l) (Zonotope.cubMapGDown T Z i l)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
