module

public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# The independent part of a polynomial zonotope

`indepZonotope` is the independent generators and the error box of `pZ` as a zonotope about the
origin. Together with `depPart` it splits the set: a point is a point of `depPart` at its factors
plus a point of this zonotope.

## Inputs
* `pZ` – polynomial zonotope

## Output
* the independent part
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The independent generators and the error box of `pZ`, as a zonotope about the origin. -/
def PolyZonotope.indepZonotope (pZ : PolyZonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) where
  h := pZ.q
  c := fun _ => zero
  G := pZ.GI
  I_error := pZ.I_error

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
