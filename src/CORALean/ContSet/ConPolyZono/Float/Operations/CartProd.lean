module

public import CORALean.ContSet.ConPolyZono.Float.Operations.PlusA
public import CORALean.ContSet.ConPolyZono.Float.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Real.Operations.PlusE
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.Global.Float.GenBlockDiag

@[expose] public section

/-!
# `ConPolyZono.cartProd`, over a floating-point scalar

CORA's `@conPolyZono/cartProd_`: the factors of the two operands stay disjoint, so both exponent
matrices are block diagonal (`PolyZonotope.plusE`), the centres stack, the dependent and the
independent generators are each `genBlockDiag` of the two, the constraint matrix is block diagonal
(`plusA`) and the right-hand sides stack (`plusB`). The error boxes stack (`Interval.append`).
Nothing is added or multiplied, so nothing rounds.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n₁ n₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.cartProd (cPZ₁ : ConPolyZono 𝕋 (Vec 𝕋 n₁)) (cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n₂)) :
    ConPolyZono 𝕋 (Vec 𝕋 (n₁ + n₂)) where
  p := cPZ₁.p + cPZ₂.p
  h := cPZ₁.h + cPZ₂.h
  q := cPZ₁.q + cPZ₂.q
  m := cPZ₁.m + cPZ₂.m
  s := cPZ₁.s + cPZ₂.s
  c := Fin.append cPZ₁.c cPZ₂.c
  G := fun l i => genBlockDiag (fun i l => cPZ₁.G l i) (fun i l => cPZ₂.G l i) i l
  E := Real.PolyZonotope.plusE cPZ₁.E cPZ₂.E
  GI := fun j i => genBlockDiag (fun i j => cPZ₁.GI j i) (fun i j => cPZ₂.GI j i) i j
  A := ConPolyZono.plusA cPZ₁.A cPZ₂.A
  b := ConPolyZono.plusB cPZ₁.b cPZ₂.b
  EC := Real.PolyZonotope.plusE cPZ₁.EC cPZ₂.EC
  err := Interval.append cPZ₁.err cPZ₂.err

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
