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


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.plus (cPZ₁ cPZ₂ : ConPolyZono α) : ConPolyZono α where
  p := cPZ₁.p + cPZ₂.p
  h := cPZ₁.h + cPZ₂.h
  q := cPZ₁.q + cPZ₂.q
  m := cPZ₁.m + cPZ₂.m
  s := cPZ₁.s + cPZ₂.s
  c := cPZ₁.c + cPZ₂.c
  G := Fin.append cPZ₁.G cPZ₂.G
  E := PolyZonotope.plusE cPZ₁.E cPZ₂.E
  GI := Fin.append cPZ₁.GI cPZ₂.GI
  A := ConPolyZono.plusA cPZ₁.A cPZ₂.A
  b := ConPolyZono.plusB cPZ₁.b cPZ₂.b
  EC := PolyZonotope.plusE cPZ₁.EC cPZ₂.EC

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
