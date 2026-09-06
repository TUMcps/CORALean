import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
import CORALean.ContSet.ConPolyZono.Real.Operations.Dependent
import CORALean.ContSet.ConPolyZono.Real.Operations.PadE
import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE

/-!
# `ConPolyZono.dependent`

Every independent generator made dependent, by giving it a fresh factor that
appears in it alone and to the first power. Not one entry is computed: the two
generator blocks are concatenated, the exponent matrices are over ℕ, and the
error box is carried across, so this operation rounds nothing at all and is
exact rather than enclosing.

It is here because `and` needs it. The agreement rows constrain the factors, and
an independent coefficient is not one, so both arguments have to have an empty
independent block before the rows are written.

The fresh factors take exponent zero in every constraint row, which is what
`padE` says.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.dependent (C : ConPolyZono 𝕋 n) : ConPolyZono 𝕋 n where
  p := C.p + C.q
  h := C.h + C.q
  q := 0
  m := C.m
  s := C.s
  c := C.c
  G := fun i => Fin.append (C.G i) (C.GI i)
  E := Real.PolyZonotope.plusE C.E (Real.PolyZonotope.identE C.q)
  GI := fun _ => Fin.elim0
  A := C.A
  b := C.b
  EC := Real.ConPolyZono.padE C.EC C.q
  err := C.err

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
