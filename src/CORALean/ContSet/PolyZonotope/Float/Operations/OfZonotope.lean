module

public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# A zonotope as the independent generators of a polynomial zonotope

CORA's `pZ + zonotope`: the zonotope's center is added to `pZ.c` and its generators go to `GI`, so
no factor is added. `Zonotope.polyZonotope` gives each generator a factor of its own instead.

## Inputs
* `Z` – zonotope

## Output
* the polynomial zonotope with `Z`'s generators as independent generators
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Z` with its generators independent: no factors, no dependent generators. -/
def Zonotope.ofIndep (Z : Zonotope (Vec 𝕋 n)) : PolyZonotope (Vec 𝕋 n) where
  p := 0
  h := 0
  q := Z.h
  c := Z.c
  G := Fin.elim0
  E := fun k => k.elim0
  GI := Z.G
  I_error := Z.I_error

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
