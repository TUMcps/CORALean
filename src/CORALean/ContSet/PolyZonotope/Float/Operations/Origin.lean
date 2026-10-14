module

public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `PolyZonotope.origin`, over a floating-point scalar

The point `0` as a polynomial zonotope with no generators of either kind, the centre
stored as `zero` and the error box at zero.
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

def PolyZonotope.origin (n : ℕ) : PolyZonotope (Vec 𝕋 n) where
  p := 0
  h := 0
  q := 0
  c := fun _ => zero
  G := Fin.elim0
  E := fun i => i.elim0
  GI := Fin.elim0
  err := Interval.origin n

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
