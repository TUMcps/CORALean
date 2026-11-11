module

public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

@[expose] public section

/-!
# The dependent part of a polynomial zonotope

`depPart` keeps the center and the dependent generators and drops the independent generators and
the error box, so its points are functions of the factors alone. The rest is `indepZonotope`: a
point of the set is a point of `depPart` at its factors plus a point of `indepZonotope`, which
tells an input that is constant in time (the first) from one that varies (the second).

## Inputs
* `pZ` – polynomial zonotope

## Output
* the dependent part
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

/-- The center and the dependent generators of `pZ`, with no independent generators and no error. -/
def PolyZonotope.depPart (pZ : PolyZonotope (Vec 𝕋 n)) : PolyZonotope (Vec 𝕋 n) where
  p := pZ.p
  h := pZ.h
  q := 0
  c := pZ.c
  G := pZ.G
  E := pZ.E
  GI := Fin.elim0
  I_error := ⟨fun _ => zero, fun _ => zero⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
