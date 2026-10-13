module

public import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
public import CORALean.ContSet.ConPolyZono.Real.Operations.Dependent
public import CORALean.ContSet.ConPolyZono.Real.Operations.PadE
public import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE

@[expose] public section

/-!
# `ConPolyZono.dependent`

Every independent generator made dependent, by giving it a fresh factor that
appears in it alone and to the first power. Not one entry is computed: the two
generator blocks are concatenated, the exponent matrices are over ℕ, and the
error box is carried across, so this operation rounds nothing at all and is
exact rather than enclosing.

It is here because `intersection` needs it. The agreement rows constrain the factors, and
an independent coefficient is not one, so both arguments have to have an empty
independent block before the rows are written.

The fresh factors take exponent zero in every constraint row, which is what
`padE` says.
-/

-- Authors:       Claude Opus 5
-- Written:       03-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.dependent (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : ConPolyZono 𝕋 (Vec 𝕋 n) where
  p := cPZ.p + cPZ.q
  h := cPZ.h + cPZ.q
  q := 0
  m := cPZ.m
  s := cPZ.s
  c := cPZ.c
  G := Fin.append cPZ.G cPZ.GI
  E := Real.PolyZonotope.plusE cPZ.E (Real.PolyZonotope.identE cPZ.q)
  GI := Fin.elim0
  A := cPZ.A
  b := cPZ.b
  EC := Real.ConPolyZono.padE cPZ.EC cPZ.q
  err := cPZ.err

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
