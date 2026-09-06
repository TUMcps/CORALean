import CORALean.ContSet.ConPolyZono.Float.Operations.MtimesResidual
import CORALean.ContSet.Interval.Float.Operations.Mtimes
import CORALean.ContSet.Interval.Float.Operations.Plus

/-!
# `ConPolyZono.mtimes`

`PolyZonotope.mtimes` with the constraint system carried along untouched. That
it *is* untouched is the whole content: the constraints live on the factors, a
map of the ambient space moves no factor, and so `A`, `b` and `EC` are copied
rather than recomputed — which is the only way a constraint block can cross a
float layer at all.

The dimension variables are `k` and `n` rather than the usual `m` and `n`: the
structure already has a field named `m`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   06-September-2026
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n k : ℕ}

def ConPolyZono.mtimes (M : Mat 𝕋 k n) (C : ConPolyZono 𝕋 n) : ConPolyZono 𝕋 k where
  p := C.p
  h := C.h
  q := C.q
  m := C.m
  s := C.s
  c := mulVecDown M C.c
  G := matMulDown M C.G
  E := C.E
  GI := matMulDown M C.GI
  A := C.A
  b := C.b
  EC := C.EC
  err := (Interval.mtimes M C.err).plus (ConPolyZono.mtimesResidual M C)

end CORALean.Float
