module

public import CORALean.ContSet.Conversion.Real.Operations.Ellipsoid_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Ellipsoid

@[expose] public section

/-!
# `Ellipsoid.cartProd`

CORA's `@ellipsoid/cartProd_.m`, which supports `'outer'` only: for two ellipsoids it is
`ellipsoid(cartProd_(interval(E), interval(S), 'exact'))`, the ellipsoid enclosing the product
of the two bounding boxes (the product of two ellipsoids is not an ellipsoid). The `'inner'` and
`'exact'` modes throw. A point operand, which CORA also handles, is `Ellipsoid.cartProdVec`.

## Inputs
* `E₁` – first ellipsoid
* `E₂` – second ellipsoid

## Output
* ellipsoid of the product of the two bounding boxes
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The ellipsoid of the product of the two bounding boxes, as CORA's `'outer'` mode. -/
noncomputable def Ellipsoid.cartProd (E₁ : Ellipsoid n) (E₂ : Ellipsoid m) : Ellipsoid (n + m) :=
  let I₁ := E₁.interval
  let I₂ := E₂.interval
  Interval.ellipsoid ⟨Fin.append I₁.inf I₂.inf, Fin.append I₁.sup I₂.sup⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
