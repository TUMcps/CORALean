module

public import CORALean.ContSet.Interval.Real.Theorems.Basic
public import CORALean.ContSet.PolyLevelSet.Real.Operations.CartProd
public import CORALean.ContSet.ConPolyZono.Real.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Real.Operations.PlusE
public import CORALean.ContSet.LevelSet.Real.Theorems.Basic

@[expose] public section

/-!
# `ConPolyZono.cartProd`

CORA's `@conPolyZono/cartProd`: `PolyZonotope.cartProd` with the two constraint
systems carried along side by side, exactly as `plus` carries them —
`PolyLevelSet.cartProd` lays the rows out block-diagonally and concatenates the bounds, so a
row of one set still reads exponent zero on every factor of the other.

The centers pair rather than add, and every generator embeds into the product
ambient type at zero in the other coordinate: the two operands no longer share
an ambient type, which is the one place this departs from `plus`.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       11-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.cartProd (cPZ₁ : ConPolyZono α) (cPZ₂ : ConPolyZono β) :
    ConPolyZono (α × β) where
  p := cPZ₁.p + cPZ₂.p
  h := cPZ₁.h + cPZ₂.h
  qI := cPZ₁.qI + cPZ₂.qI
  c := (cPZ₁.c, cPZ₂.c)
  G := Fin.append (fun i => (cPZ₁.G i, (0 : β))) (fun i => ((0 : α), cPZ₂.G i))
  E := PolyZonotope.plusE cPZ₁.E cPZ₂.E
  GI := Fin.append (fun j => (cPZ₁.GI j, (0 : β))) (fun j => ((0 : α), cPZ₂.GI j))
  cons := cPZ₁.cons.cartProd cPZ₂.cons
  cons_eq := LevelSet.append_op_eq cPZ₁.cons_eq cPZ₂.cons_eq
  cons_dom := Interval.append_eq_unit cPZ₁.cons_dom cPZ₂.cons_dom

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
