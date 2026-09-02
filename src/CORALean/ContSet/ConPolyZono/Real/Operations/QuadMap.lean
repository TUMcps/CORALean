import CORALean.ContSet.ConPolyZono.Real.Operations.Dependent
import CORALean.ContSet.Conversion.Real.ConPolyZono_to_PolyZonotope
import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMap

/-!
# `ConPolyZono.quadMap`

CORA's `@conPolyZono/quadMap`. `PolyZonotope`'s carries over unchanged, and that
it does is the point of the file: a quadratic map touches the centre, the
generators and the exponent matrix, and the constraint system reads none of
those. `quadMapDep` keeps the factor count, so `A`, `b` and `EC` pass through
untouched and say of the image exactly what they said of the argument.

The generators and exponent columns are `PolyZonotope`'s, taken at the
polynomial zonotope this set is without its constraints. That is the enclosing
conversion used as bookkeeping rather than as an enclosure: `quadMapG` and
`quadMapE` read only the fields the two representations share, and dropping
constraints does not change a field.

`quadMap` runs `quadMapDep` on `dependent`, exactly as `PolyZonotope.quadMap`
does and for the same reason: the expansion is stated on a set whose
coefficients are all dependent. Here `dependent` also widens the constraints
with zero rows for the fresh factors, which is what keeps the two arrangements
in step.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

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

def ConPolyZono.quadMap (Q : Fin k → Mat ℝ n n) (C : ConPolyZono (Vec ℝ n)) :
    ConPolyZono (Vec ℝ k) :=
  ConPolyZono.quadMapDep Q C.dependent

end CORALean.Real
