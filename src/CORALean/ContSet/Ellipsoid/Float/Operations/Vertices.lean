module

public import CORALean.ContSet.Ellipsoid.Float.Operations.BoxRadius
public import CORALean.Global.Float.Sqrt

@[expose] public section

/-!
# `Ellipsoid.vertices`, over a floating-point scalar

The one-dimensional case, the only one CORA supports. The ends are the center give or take the
half-width `ρ = √Q₀₀` (`boxRadius`, `k` Newton steps, rounded up), the lower one rounded down and
the upper one up, each shifted by its end of the error box. Both are always returned: CORA's
single-vertex case (the two agree within tolerance) is not modelled, so for a point the list
holds that point twice. The statement is an outer one, the ellipsoid lies in the hull of the two
points.

## Inputs
* `k` – Newton steps of the root
* `E` – one-dimensional ellipsoid

## Output
* the two end points of `E`
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def Ellipsoid.vertices (k : ℕ) (E : Ellipsoid 𝕋 1) : List (Vec 𝕋 1) :=
  let ρ := Ellipsoid.boxRadius k E 0
  [fun _ => addDown (subDown (E.q 0) ρ) (E.I_error.inf 0),
   fun _ => addUp (addUp (E.q 0) ρ) (E.I_error.sup 0)]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
