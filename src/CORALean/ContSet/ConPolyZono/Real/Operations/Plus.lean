import CORALean.ContSet.ConPolyZono.Real.Operations.PlusA
import CORALean.ContSet.ConPolyZono.Real.Operations.PlusB
import CORALean.ContSet.PolyZonotope.Real.Operations.Plus

/-!
# `ConPolyZono.plus`

CORA's `@conPolyZono/plus`: `PolyZonotope.plus` with the two constraint systems
carried along side by side.

Nothing couples the two sets, so nothing may be identified: the factors are laid
out block-diagonally by `PolyZonotope.plusE`, and the constraint *rows* are laid
out block-diagonally too, by `plusA`. A row of one set then reads exponent zero
on every factor of the other, so it constrains the factors it came with and no
others — which is what makes the sum exact rather than too small.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

def ConPolyZono.plus (C₁ C₂ : ConPolyZono α) : ConPolyZono α where
  p := C₁.p + C₂.p
  h := C₁.h + C₂.h
  q := C₁.q + C₂.q
  m := C₁.m + C₂.m
  s := C₁.s + C₂.s
  c := C₁.c + C₂.c
  G := Fin.append C₁.G C₂.G
  E := PolyZonotope.plusE C₁.E C₂.E
  GI := Fin.append C₁.GI C₂.GI
  A := ConPolyZono.plusA C₁.A C₂.A
  b := ConPolyZono.plusB C₁.b C₂.b
  EC := PolyZonotope.plusE C₁.EC C₂.EC

end CORALean.Real
