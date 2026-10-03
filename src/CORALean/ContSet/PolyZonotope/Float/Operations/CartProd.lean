import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
import CORALean.ContSet.PolyZonotope.Real.Operations.PlusE
import CORALean.ContSet.Interval.Float.Operations.Append
import CORALean.Global.Float.GenBlockDiag

/-!
# `PolyZonotope.cartProd`, over a floating-point scalar

CORA's `@polyZonotope/cartProd_`: the factors of the two operands stay disjoint, so the exponent
matrix is block diagonal (`PolyZonotope.plusE`), the centres stack, and the dependent and the
independent generators are each `genBlockDiag` of the two. The error boxes stack
(`Interval.append`). Nothing is added or multiplied, so nothing rounds.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n₁ n₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.cartProd (pZ₁ : PolyZonotope 𝕋 n₁) (pZ₂ : PolyZonotope 𝕋 n₂) :
    PolyZonotope 𝕋 (n₁ + n₂) where
  p := pZ₁.p + pZ₂.p
  h := pZ₁.h + pZ₂.h
  q := pZ₁.q + pZ₂.q
  c := Fin.append pZ₁.c pZ₂.c
  G := genBlockDiag pZ₁.G pZ₂.G
  E := Real.PolyZonotope.plusE pZ₁.E pZ₂.E
  GI := genBlockDiag pZ₁.GI pZ₂.GI
  err := Interval.append pZ₁.err pZ₂.err

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
