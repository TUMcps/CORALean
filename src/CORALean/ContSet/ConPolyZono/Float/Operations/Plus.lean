module

public import CORALean.ContSet.ConPolyZono.Float.Operations.Basic
public import CORALean.ContSet.ConPolyZono.Real.Operations.Plus
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.PolyZonotope.Float.Operations.Plus
public import CORALean.ContSet.PolyLevelSet.Float.Operations.CartProd
public import CORALean.ContSet.LevelSet.Real.Theorems.Basic

@[expose] public section

/-!
# `ConPolyZono.plus`

`PolyZonotope.plus` with the two constraint systems carried along side by side,
and the reason it refines is that the carrying is pure bookkeeping: the float
`PolyLevelSet.cartProd` places the two matrices block-diagonally with `zero` in the off-blocks
and `b` and `b_error` concatenate, so not one entry of the constraint system is computed. Only the
center rounds, exactly as for an unconstrained polynomial zonotope.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.plus (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n)) : ConPolyZono 𝕋 (Vec 𝕋 n) where
  p := cPZ₁.p + cPZ₂.p
  h := cPZ₁.h + cPZ₂.h
  qI := cPZ₁.qI + cPZ₂.qI
  c := fun i => addDown (cPZ₁.c i) (cPZ₂.c i)
  G := Fin.append cPZ₁.G cPZ₂.G
  E := Real.PolyZonotope.plusE cPZ₁.E cPZ₂.E
  GI := Fin.append cPZ₁.GI cPZ₂.GI
  cons := cPZ₁.cons.cartProd cPZ₂.cons
  cons_eq := Real.LevelSet.append_op_eq cPZ₁.cons_eq cPZ₂.cons_eq
  cons_dom := Interval.append_eq_unit cPZ₁.cons_dom cPZ₂.cons_dom
  I_error := (cPZ₁.I_error.plus cPZ₂.I_error).plus (PolyZonotope.centerResidual cPZ₁.c cPZ₂.c)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
