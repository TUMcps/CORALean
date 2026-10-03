import CORALean.ContSet.ConPolyZono.Float.Operations.PlusA
import CORALean.ContSet.ConPolyZono.Float.Operations.PlusB
import CORALean.ContSet.PolyZonotope.Real.Operations.PlusE
import CORALean.ContSet.Interval.Float.Operations.Append
import CORALean.Global.Float.GenBlockDiag

/-!
# `ConPolyZono.cartProd`, over a floating-point scalar

CORA's `@conPolyZono/cartProd_`: the factors of the two operands stay disjoint, so both exponent
matrices are block diagonal (`PolyZonotope.plusE`), the centres stack, the dependent and the
independent generators are each `genBlockDiag` of the two, the constraint matrix is block diagonal
(`plusA`) and the right-hand sides stack (`plusB`). The error boxes stack (`Interval.append`).
Nothing is added or multiplied, so nothing rounds.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n₁ n₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.cartProd (cPZ₁ : ConPolyZono 𝕋 n₁) (cPZ₂ : ConPolyZono 𝕋 n₂) :
    ConPolyZono 𝕋 (n₁ + n₂) where
  p := cPZ₁.p + cPZ₂.p
  h := cPZ₁.h + cPZ₂.h
  q := cPZ₁.q + cPZ₂.q
  m := cPZ₁.m + cPZ₂.m
  s := cPZ₁.s + cPZ₂.s
  c := Fin.append cPZ₁.c cPZ₂.c
  G := genBlockDiag cPZ₁.G cPZ₂.G
  E := Real.PolyZonotope.plusE cPZ₁.E cPZ₂.E
  GI := genBlockDiag cPZ₁.GI cPZ₂.GI
  A := ConPolyZono.plusA cPZ₁.A cPZ₂.A
  b := ConPolyZono.plusB cPZ₁.b cPZ₂.b
  EC := Real.PolyZonotope.plusE cPZ₁.EC cPZ₂.EC
  err := Interval.append cPZ₁.err cPZ₂.err

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
