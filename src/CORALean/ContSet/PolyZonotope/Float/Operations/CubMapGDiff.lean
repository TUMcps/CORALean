module

public import CORALean.ContSet.PolyZonotope.Float.Operations.CubMapGDown
public import CORALean.ContSet.PolyZonotope.Float.Operations.CubMapGUp

@[expose] public section

/-!
# `PolyZonotope.cubMapGDiff`

How far a stored generator of `PolyZonotope.cubMap` can be from the exact one: the gap between its
two roundings, which a monomial in `[-1, 1]` then spreads either way.
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

def PolyZonotope.cubMapGDiff (T : Fin m → Fin n → Mat 𝕋 n n) (pZ : PolyZonotope (Vec 𝕋 n)) :
    Fin m → Fin ((pZ.h + 1) * (pZ.h + 1) * (pZ.h + 1)) → 𝕋 :=
  fun i l => subUp (PolyZonotope.cubMapGUp T pZ i l) (PolyZonotope.cubMapGDown T pZ i l)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
