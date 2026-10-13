import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
import CORALean.ContSet.Interval.Float.Operations.Origin

/-!
# `ConPolyZono.origin`, over a floating-point scalar

The point `0` as a constrained polynomial zonotope with no generators and an empty
constraint system, the centre stored as `zero` and both boxes at zero.
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

def ConPolyZono.origin (n : ℕ) : ConPolyZono 𝕋 (Vec 𝕋 n) where
  p := 0
  h := 0
  q := 0
  m := 0
  s := 0
  c := fun _ => zero
  G := Fin.elim0
  E := fun i => i.elim0
  GI := Fin.elim0
  A := fun i => i.elim0
  b := Interval.origin 0
  EC := fun i => i.elim0
  err := Interval.origin n

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
