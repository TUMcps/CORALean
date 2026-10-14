module

public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
public import CORALean.ContSet.PolyZonotope.Real.Operations.PlusE
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.Global.Float.GenBlockDiag

@[expose] public section

/-!
# `PolyZonotope.cartProd`, over a floating-point scalar

CORA's `@polyZonotope/cartProd_`: the factors of the two operands stay disjoint, so the exponent
matrix is block diagonal (`PolyZonotope.plusE`), the centres stack, and the dependent and the
independent generators are each `genBlockDiag` of the two. The error boxes stack
(`Interval.append`). Nothing is added or multiplied, so nothing rounds.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n₁ n₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.cartProd (pZ₁ : PolyZonotope (Vec 𝕋 n₁)) (pZ₂ : PolyZonotope (Vec 𝕋 n₂)) :
    PolyZonotope (Vec 𝕋 (n₁ + n₂)) where
  p := pZ₁.p + pZ₂.p
  h := pZ₁.h + pZ₂.h
  q := pZ₁.q + pZ₂.q
  c := Fin.append pZ₁.c pZ₂.c
  G := fun l i => genBlockDiag (fun i l => pZ₁.G l i) (fun i l => pZ₂.G l i) i l
  E := Real.PolyZonotope.plusE pZ₁.E pZ₂.E
  GI := fun j i => genBlockDiag (fun i j => pZ₁.GI j i) (fun i j => pZ₂.GI j i) i j
  I_error := Interval.append pZ₁.I_error pZ₂.I_error

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
