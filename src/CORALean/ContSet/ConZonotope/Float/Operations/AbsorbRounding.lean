module

public import CORALean.ContSet.ConZonotope.Float.ConZonotope
public import CORALean.ContSet.PolyZonotope.Float.Operations.ErrorBound
public import CORALean.ContSet.HPolytope.Float.Operations.PadLeft

@[expose] public section

/-!
# `ConZonotope.absorbRounding`

The error box made into coefficients: one fresh generator per coordinate, as long as the box's
larger endpoint (`errorBound`, which rounds nothing), on a coefficient the constraints leave
free. A quadratic map is not additive, so a nominal part and a box cannot travel through it
separately; emptying the box first is what `quadMap` needs, as for `PolyZonotope.absorbRounding`.

## Inputs
* `cZ` – float constrained zonotope

## Output
* the same set with the error box turned into generators
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.absorbRounding (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : ConZonotope 𝕋 (Vec 𝕋 n) where
  h := cZ.h + n
  c := cZ.c
  G := Fin.append cZ.G (diagonalBlock (PolyZonotope.errorBound cZ.I_error))
  -- the polytope keeps its own slacks `b_error` and `be_error`, padded with it
  P := cZ.P.padLeft n
  I_error := ⟨fun _ => zero, fun _ => zero⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
