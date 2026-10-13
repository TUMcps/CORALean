module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Map
public import Mathlib.Algebra.Module.Equiv.Basic

@[expose] public section

/-!
# `ConPolyZono.project`

CORA's `@conPolyZono/project`: the centre and both generator matrices at the chosen coordinates,
with exponents, factors and constraint untouched. `dims` may repeat or reorder coordinates.
Reading coordinates is linear, so this is `map` at the selection map, and `project_exact` is
`map_exact`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.project (cPZ : ConPolyZono (Vec ℝ n))
    (dims : Fin m → Fin n) : ConPolyZono (Vec ℝ m) :=
  cPZ.map (LinearMap.funLeft ℝ ℝ dims)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
