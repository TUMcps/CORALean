module

public import CORALean.ContSet.ConZonotope.Float.ConZonotope
public import CORALean.ContSet.HPolytope.Float.Operations.CartProd
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.Global.Float.GenBlockDiag

@[expose] public section

/-!
# `ConZonotope.cartProd`, over a floating-point scalar

CORA's `@conZonotope/cartProd_`: the centers stack, the generators are block diagonal
(`genBlockDiag`), and the constraints of the two operands stay on their own coefficients, the
polytope being the product of the two coefficient polytopes (`HPolytope.cartProd`). Nothing is
added or multiplied, so nothing rounds, and the error boxes stack (`Interval.append`).

## Inputs
* `cZ₁` – first constrained zonotope
* `cZ₂` – second constrained zonotope

## Output
* the Cartesian product
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n₁ n₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.cartProd (cZ₁ : ConZonotope 𝕋 (Vec 𝕋 n₁)) (cZ₂ : ConZonotope 𝕋 (Vec 𝕋 n₂)) :
    ConZonotope 𝕋 (Vec 𝕋 (n₁ + n₂)) where
  h := cZ₁.h + cZ₂.h
  c := Fin.append cZ₁.c cZ₂.c
  G := fun j i => genBlockDiag (fun i j => cZ₁.G j i) (fun i j => cZ₂.G j i) i j
  P := cZ₁.P.cartProd cZ₂.P
  I_error := Interval.append cZ₁.I_error cZ₂.I_error

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
