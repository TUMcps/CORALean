import CORALean.ContSet.Interval.Float.Operations.Project
import CORALean.ContSet.ConPolyZono.Float.ConPolyZono

/-!
# `ConPolyZono.project` over a floating-point scalar

The centre and the rows of both generator blocks at the chosen coordinates; the exponent
matrices and the constraint system constrain the factors, not the coordinates, and are copied.
The error box is projected with `Interval.project`. Selecting coordinates does no arithmetic,
so nothing rounds.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.project (cPZ : ConPolyZono 𝕋 n) (dims : Fin m → Fin n) : ConPolyZono 𝕋 m where
  p := cPZ.p
  h := cPZ.h
  q := cPZ.q
  m := cPZ.m
  s := cPZ.s
  c := fun k => cPZ.c (dims k)
  G := fun k l => cPZ.G (dims k) l
  E := cPZ.E
  GI := fun k j => cPZ.GI (dims k) j
  A := cPZ.A
  b := cPZ.b
  EC := cPZ.EC
  err := cPZ.err.project dims

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
