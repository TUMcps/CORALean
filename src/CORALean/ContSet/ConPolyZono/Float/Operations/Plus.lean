import CORALean.ContSet.ConPolyZono.Float.Operations.PlusA
import CORALean.ContSet.ConPolyZono.Float.Operations.PlusB
import CORALean.ContSet.ConPolyZono.Real.Operations.Plus
import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.PolyZonotope.Float.Operations.Plus

/-!
# `ConPolyZono.plus`

`PolyZonotope.plus` with the two constraint systems carried along side by side,
and the reason it refines is that the carrying is pure bookkeeping: `plusA`
places the two matrices block-diagonally with `zero` in the off-blocks and `b`
concatenates, so not one entry of the constraint system is computed. Only the
centre rounds, exactly as for an unconstrained polynomial zonotope.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

def ConPolyZono.plus (C₁ C₂ : ConPolyZono 𝕋 n) : ConPolyZono 𝕋 n where
  p := C₁.p + C₂.p
  h := C₁.h + C₂.h
  q := C₁.q + C₂.q
  m := C₁.m + C₂.m
  s := C₁.s + C₂.s
  c := fun i => addDown (C₁.c i) (C₂.c i)
  G := fun i => Fin.append (C₁.G i) (C₂.G i)
  E := Real.PolyZonotope.plusE C₁.E C₂.E
  GI := fun i => Fin.append (C₁.GI i) (C₂.GI i)
  A := ConPolyZono.plusA C₁.A C₂.A
  b := ConPolyZono.plusB C₁.b C₂.b
  EC := Real.PolyZonotope.plusE C₁.EC C₂.EC
  err := (C₁.err.plus C₂.err).plus (PolyZonotope.centerResidual C₁.c C₂.c)

end CORALean.Float
