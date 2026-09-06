import CORALean.ContSet.ConPolyZono.Float.Operations.DropRadius

/-!
# `ConPolyZono.reduceBy`, over a floating-point scalar

Split out of `Reduce.lean` (issue #62): read again by `reduceGirard` in this
directory and by `Theorems/ReduceByOuter.lean` and
`Theorems/ReduceGirardOrderLe.lean`, all outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n d r dI rI : ℕ}

/-- CORA's reduction at a given pair of partitions, sound for every one of them:
kept dependent generators keep their exponent columns, kept independent ones are
copied, and the rest becomes a box no longer tied to the factors. -/
def ConPolyZono.reduceBy (C : ConPolyZono 𝕋 n)
    (partD : Split (Fin C.h) into (Fin d) and (Fin r))
    (partI : Split (Fin C.q) into (Fin dI) and (Fin rI)) : ConPolyZono 𝕋 n where
  p := C.p
  h := d
  q := dI + n
  m := C.m
  s := C.s
  c := C.c
  G := fun i l => C.G i (partD.left l)
  E := fun k l => C.E k (partD.left l)
  GI := fun i => Fin.append (fun j => C.GI i (partI.left j))
    (diagonalBlock (C.dropRadius partD partI) i)
  A := C.A
  b := C.b
  EC := C.EC
  err := C.err

end CORALean.Float
