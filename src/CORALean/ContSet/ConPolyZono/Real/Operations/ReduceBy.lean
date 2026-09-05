import CORALean.ContSet.ConPolyZono.Real.Operations.DropRadius

/-!
# `ConPolyZono.reduceBy`

Partitions both generator blocks: what `partD.left` and `partI.left` name is
kept, with the former's exponent columns, and the rest is absorbed into a
diagonal block of `n` independent generators. The constraints stand.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {n d r dI rI : ℕ}

/-- Partitions both generator blocks: what `partD.left` and `partI.left` name is
kept, with the former's exponent columns, and the rest is absorbed into a
diagonal block of `n` independent generators. The constraints stand. -/
def ConPolyZono.reduceBy (C : ConPolyZono (Vec ℝ n))
    (partD : Split (Fin C.h) into (Fin d) and (Fin r))
    (partI : Split (Fin C.q) into (Fin dI) and (Fin rI)) : ConPolyZono (Vec ℝ n) where
  p := C.p
  h := d
  q := dI + n
  m := C.m
  s := C.s
  c := C.c
  G := fun l => C.G (partD.left l)
  E := fun k l => C.E k (partD.left l)
  GI := Fin.append (fun j => C.GI (partI.left j))
          (Matrix.diagonal (C.dropRadius partD partI))
  A := C.A
  b := C.b
  EC := C.EC

end CORALean.Real
