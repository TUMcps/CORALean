import CORALean.ContSet.Conversion.Real.ConPolyZono_to_PolyZonotope
import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMap

/-!
# `ConPolyZono.quadMapDep`

The map on a set whose coefficients are all dependent. Sound only there, so
nothing calls it directly. Touches the centre, generators and exponent matrix
of the enclosing polynomial zonotope; the constraint system reads none of
those, so `A`, `b` and `EC` pass through untouched.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {n k : ℕ}

/-- The map on a set whose coefficients are all dependent. Sound only there, so
nothing calls it directly. -/
def ConPolyZono.quadMapDep (Q : Fin k → Mat ℝ n n) (C : ConPolyZono (Vec ℝ n)) :
    ConPolyZono (Vec ℝ k) where
  p := C.p
  h := (C.h + 1) * (C.h + 1)
  q := 0
  m := C.m
  s := C.s
  c := 0
  G := PolyZonotope.quadMapG Q C.polyZonotope
  E := PolyZonotope.quadMapE C.polyZonotope
  GI := Fin.elim0
  A := C.A
  b := C.b
  EC := C.EC

end CORALean.Real
