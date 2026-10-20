module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.ConZonotope.Float.ConZonotope

@[expose] public section

/-!
# `ConZonotope.project` over a floating-point scalar

The center and every generator row at the chosen coordinates, the constraint polytope untouched
(it constrains the factors, not the coordinates), and the error box projected with
`Interval.project`. Selecting coordinates does no arithmetic, so nothing rounds.

## Inputs
* `cZ` – float constrained zonotope
* `dims` – retained dimensions

## Output
* the projection onto the retained dimensions
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.project (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (dims : Fin m → Fin n) : ConZonotope
    𝕋 (Vec 𝕋 m) where
  h := cZ.h
  c := fun k => cZ.c (dims k)
  G := fun j k => cZ.G j (dims k)
  P := cZ.P
  I_error := cZ.I_error.project dims

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
