module

public import CORALean.ContSet.VPolytope.Float.VPolytope
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `VPolytope.origin`, over a floating-point scalar

CORA's `polytope.origin(n)` in its vertex form: the single vertex `0`, stored as `zero`, and
the error box at the point `0`.

## Inputs
* `n` – dimension

## Output
* polytope with the origin as its only vertex
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def VPolytope.origin (n : ℕ) : VPolytope (Vec 𝕋 n) where
  k := 1
  V := fun _ _ => zero
  I_error := Interval.origin n

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
