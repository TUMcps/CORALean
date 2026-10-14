module

public import CORALean.ContSet.ConPolyZono.Real.Operations.PlusA
public import CORALean.ContSet.ConPolyZono.Real.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Real.Operations.PlusE

@[expose] public section

/-!
# `ConPolyZono.cartProd`

CORA's `@conPolyZono/cartProd`: `PolyZonotope.cartProd` with the two constraint
systems carried along side by side, exactly as `plus` carries them — `plusA`
lays the rows out block-diagonally and `plusB` concatenates the bounds, so a
row of one set still reads exponent zero on every factor of the other.

The centres pair rather than add, and every generator embeds into the product
ambient type at zero in the other coordinate: the two operands no longer share
an ambient type, which is the one place this departs from `plus`.
-/

-- Authors:       Claude Opus 5
-- Written:       11-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.cartProd (cPZ₁ : ConPolyZono α) (cPZ₂ : ConPolyZono β) :
    ConPolyZono (α × β) where
  p := cPZ₁.p + cPZ₂.p
  h := cPZ₁.h + cPZ₂.h
  q := cPZ₁.q + cPZ₂.q
  m := cPZ₁.m + cPZ₂.m
  s := cPZ₁.s + cPZ₂.s
  c := (cPZ₁.c, cPZ₂.c)
  G := Fin.append (fun i => (cPZ₁.G i, (0 : β))) (fun i => ((0 : α), cPZ₂.G i))
  E := PolyZonotope.plusE cPZ₁.E cPZ₂.E
  GI := Fin.append (fun j => (cPZ₁.GI j, (0 : β))) (fun j => ((0 : α), cPZ₂.GI j))
  A := ConPolyZono.plusA cPZ₁.A cPZ₂.A
  b := ConPolyZono.plusB cPZ₁.b cPZ₂.b
  EC := PolyZonotope.plusE cPZ₁.EC cPZ₂.EC

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
