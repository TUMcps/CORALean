module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Ellipsoid.Float.Ellipsoid

@[expose] public section

/-!
# `Ellipsoid.project` over a floating-point scalar

CORA's `@ellipsoid/project`: the shape matrix at the chosen rows and columns, `E.Q(dims, dims)`,
the center at the chosen coordinates, and the error box projected with `Interval.project`.
Selecting entries does no arithmetic, so nothing rounds.

## Inputs
* `E` – ellipsoid
* `dims` – kept coordinates

## Output
* `E` projected onto `dims`
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Ellipsoid.project (E : Ellipsoid 𝕋 n) (dims : Fin m → Fin n) : Ellipsoid 𝕋 m where
  Q := fun i j => E.Q (dims i) (dims j)
  q := fun i => E.q (dims i)
  I_error := E.I_error.project dims

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
