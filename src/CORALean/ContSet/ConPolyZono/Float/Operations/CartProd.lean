module

public import CORALean.ContSet.ConPolyZono.Float.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Real.Operations.PlusE
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.Global.Float.GenBlockDiag
public import CORALean.ContSet.PolyLevelSet.Float.Operations.CartProd
public import CORALean.ContSet.LevelSet.Real.Theorems.Basic

@[expose] public section

/-!
# `ConPolyZono.cartProd`, over a floating-point scalar

CORA's `@conPolyZono/cartProd_`: the factors of the two operands stay disjoint, so both exponent
matrices are block diagonal (`PolyZonotope.plusE`), the centers stack, the dependent and the
independent generators are each `genBlockDiag` of the two, and the constraint is the float
`PolyLevelSet.cartProd` of the two, rows and slacks stacked, the nominal part being the
product of the two (`Real.ConPolyZono.relax_cartProd`). The error boxes stack (`Interval.append`).
Nothing is added or multiplied, so nothing rounds.
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n₁ n₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.cartProd (cPZ₁ : ConPolyZono 𝕋 (Vec 𝕋 n₁)) (cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n₂)) :
    ConPolyZono 𝕋 (Vec 𝕋 (n₁ + n₂)) where
  p := cPZ₁.p + cPZ₂.p
  h := cPZ₁.h + cPZ₂.h
  qI := cPZ₁.qI + cPZ₂.qI
  c := Fin.append cPZ₁.c cPZ₂.c
  G := fun l i => genBlockDiag (fun i l => cPZ₁.G l i) (fun i l => cPZ₂.G l i) i l
  E := Real.PolyZonotope.plusE cPZ₁.E cPZ₂.E
  GI := fun j i => genBlockDiag (fun i j => cPZ₁.GI j i) (fun i j => cPZ₂.GI j i) i j
  cons := cPZ₁.cons.cartProd cPZ₂.cons
  cons_eq := Real.LevelSet.append_op_eq cPZ₁.cons_eq cPZ₂.cons_eq
  I_error := Interval.append cPZ₁.I_error cPZ₂.I_error

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
