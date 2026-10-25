module

public import CORALean.ContSet.Ellipsoid.Real.Operations.SupportBound

@[expose] public section

/-!
# `Ellipsoid.vertices`

CORA's `@ellipsoid/vertices_.m`, which supports the one-dimensional case only (it throws for
`dim(E) > 1`): the two points attaining the support function in the directions `-1` and `1`, or
the single one when they agree (`IsWithinTol` at the default tolerance, here exact equality). In one
dimension the points are `q ∓ ‖G₀‖₂`, the support values of `Ellipsoid.supportBound`.

## Inputs
* `E` – one-dimensional ellipsoid

## Output
* lower and upper end, once if they agree
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The vertices of a one-dimensional ellipsoid: the lower and upper end, once if they agree. -/
noncomputable def Ellipsoid.vertices (E : Ellipsoid 1) : List (Vec ℝ 1) :=
  let hi := (E.supportBound (LinearMap.proj 0)).val
  let lo := -(E.supportBound (-LinearMap.proj 0)).val
  if lo = hi then [fun _ => lo] else [fun _ => lo, fun _ => hi]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
