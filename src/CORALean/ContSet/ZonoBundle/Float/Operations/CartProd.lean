module

public import CORALean.ContSet.ZonoBundle.Float.ZonoBundle
public import CORALean.ContSet.Zonotope.Float.Operations.CartProd

@[expose] public section

/-!
# `ZonoBundle.cartProd`, over a floating-point scalar

CORA's `@zonoBundle/cartProd_`: the Cartesian product of two intersections is the intersection of
the products of all pairs of members, `k₁ · k₂` of them, member `(i, j)` at index
`i * k₂ + j` (`finProdFinEquiv`). Each product is `Zonotope.cartProd`, which does not round.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n₁ n₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.cartProd (zB₁ : ZonoBundle (Vec 𝕋 n₁)) (zB₂ : ZonoBundle (Vec 𝕋 n₂)) :
    ZonoBundle (Vec 𝕋 (n₁ + n₂)) where
  k := zB₁.k * zB₂.k
  Z := fun p =>
    let ij := finProdFinEquiv.symm p
    Zonotope.cartProd (zB₁.Z ij.1) (zB₂.Z ij.2)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
