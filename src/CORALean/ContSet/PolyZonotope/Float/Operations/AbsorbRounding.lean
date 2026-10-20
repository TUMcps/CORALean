module

public import CORALean.ContSet.PolyZonotope.Float.Operations.ErrorBound
public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
public import CORALean.ContSet.PolyZonotope.Real.Operations.Dependent
public import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE

@[expose] public section

/-!
# `PolyZonotope.absorbRounding`

Every free coefficient made dependent, by giving it a fresh factor that appears
in it alone and to the first power. The exact layer frees the independent
generators; here the error box is a second block of free coefficients, freed the
same way, leaving `q = 0` and an empty box. `quadMap` needs that, a quadratic map
not being additive. Emptying the box costs no rounding: `errorBound` takes the
larger endpoint magnitude (`maximum`, `absolute` are exact), not a midpoint.

## Inputs
* `pZ` – polynomial zonotope

## Output
* polynomial zonotope with its error box turned into independent generators
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.absorbRounding (pZ : PolyZonotope (Vec 𝕋 n)) : PolyZonotope (Vec 𝕋 n) where
  p := pZ.p + (pZ.q + n)
  h := pZ.h + (pZ.q + n)
  q := 0
  c := pZ.c
  G := fun l i => Fin.append (fun l => pZ.G l i)
    (Fin.append (fun j => pZ.GI j i) (diagonalBlock (PolyZonotope.errorBound pZ.I_error) i)) l
  E := Real.PolyZonotope.plusE pZ.E (Real.PolyZonotope.identE (pZ.q + n))
  GI := Fin.elim0
  I_error := ⟨fun _ => zero, fun _ => zero⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
