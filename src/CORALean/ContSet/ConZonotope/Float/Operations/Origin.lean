module

public import CORALean.ContSet.ConZonotope.Float.ConZonotope
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.HPolytope.Float.Operations.Fullspace

@[expose] public section

/-!
# `ConZonotope.origin`, over a floating-point scalar

The point `0` as a constrained zonotope with no generators and no constraints, the
center stored as `zero` and the error box at zero.
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

def ConZonotope.origin (n : ℕ) : ConZonotope 𝕋 (Vec 𝕋 n) where
  h := 0
  c := fun _ => zero
  G := Fin.elim0
  P := HPolytope.fullspace 𝕋 0
  I_error := Interval.origin n

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
