module

public import CORALean.ContSet.Ellipsoid.Float.Ellipsoid
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `Ellipsoid.origin`, over a floating-point scalar

The point `0` as an ellipsoid with no generators, the centre stored as `zero` and
the error box at zero.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Ellipsoid.origin (n : ℕ) : Ellipsoid 𝕋 n where
  k := 0
  q := fun _ => zero
  G := fun _ j => j.elim0
  err := Interval.origin n

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
