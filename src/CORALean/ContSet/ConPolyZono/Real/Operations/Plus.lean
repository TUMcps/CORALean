module

public import CORALean.ContSet.Interval.Real.Theorems.Basic
public import CORALean.ContSet.PolyLevelSet.Real.Operations.CartProd
public import CORALean.ContSet.ConPolyZono.Real.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Real.Operations.Plus
public import CORALean.ContSet.LevelSet.Real.Theorems.Basic

@[expose] public section

/-!
# `ConPolyZono.plus`

CORA's `@conPolyZono/plus`: `PolyZonotope.plus` with the two constraint systems
carried along side by side.

Nothing couples the two sets, so nothing may be identified: the factors are laid
out block-diagonally by `PolyZonotope.plusE`, and the constraint is the product of the two,
`PolyLevelSet.cartProd`, its rows block-diagonal too. A row of one set then reads exponent zero
on every factor of the other, so it constrains the factors it came with and no
others — which is what makes the sum exact rather than too small.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.plus (cPZ₁ cPZ₂ : ConPolyZono α) : ConPolyZono α where
  p := cPZ₁.p + cPZ₂.p
  h := cPZ₁.h + cPZ₂.h
  qI := cPZ₁.qI + cPZ₂.qI
  c := cPZ₁.c + cPZ₂.c
  G := Fin.append cPZ₁.G cPZ₂.G
  E := PolyZonotope.plusE cPZ₁.E cPZ₂.E
  GI := Fin.append cPZ₁.GI cPZ₂.GI
  cons := cPZ₁.cons.cartProd cPZ₂.cons
  cons_eq := LevelSet.append_op_eq cPZ₁.cons_eq cPZ₂.cons_eq
  cons_dom := Interval.append_eq_unit cPZ₁.cons_dom cPZ₂.cons_dom

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
