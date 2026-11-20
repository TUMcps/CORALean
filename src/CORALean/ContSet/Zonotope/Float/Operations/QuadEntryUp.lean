module

public import CORALean.ContSet.PolyZonotope.Float.Operations.QuadUp

@[expose] public section

/-!
# `Zonotope.quadEntryUp`, over a floating-point scalar

The entry `uᵀ Q v` of a quadratic map, rounded up: the row `Qᵀ u` bracketed, then its dot product
with `v`. CORA.cpp's order: `(u' Q) v`, each sum nested to the right.

## Inputs
* `Q` – matrix of the quadratic form
* `u` – left vector
* `v` – right vector

## Output
* `uᵀ Q v` rounded up
-/

-- Authors:       Claude Opus 5.5
-- Written:       20-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.quadEntryUp (Q : Mat 𝕋 n n) (u v : Vec 𝕋 n) : 𝕋 :=
  PolyZonotope.quadUp v (mulVecDown (fun k j => Q j k) u) (mulVecUp (fun k j => Q j k) u)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
