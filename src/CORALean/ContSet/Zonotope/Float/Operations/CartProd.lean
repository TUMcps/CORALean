module

public import CORALean.ContSet.Zonotope.Float.Zonotope
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.Global.Float.GenBlockDiag

@[expose] public section

/-!
# `Zonotope.cartProd`, over a floating-point scalar

CORA's `@zonotope/cartProd_`: the centres stack, the generators are block diagonal, and the error
boxes stack (`Interval.append`). Nothing is added or multiplied, so nothing rounds: `G` is
`genBlockDiag` of the two stored matrices, each padded with zeros on the side of the other operand.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n₁ n₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.cartProd (Z₁ : Zonotope (Vec 𝕋 n₁)) (Z₂ : Zonotope (Vec 𝕋 n₂)) :
    Zonotope (Vec 𝕋 (n₁ + n₂)) where
  h := Z₁.h + Z₂.h
  c := Fin.append Z₁.c Z₂.c
  G := fun j i => genBlockDiag (fun i j => Z₁.G j i) (fun i j => Z₂.G j i) i j
  E := Interval.append Z₁.E Z₂.E

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
