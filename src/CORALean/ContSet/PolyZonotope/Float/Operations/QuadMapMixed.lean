import CORALean.ContSet.PolyZonotope.Float.Operations.Bilin
import CORALean.ContSet.PolyZonotope.Float.Operations.CartProd
import CORALean.ContSet.PolyZonotope.Float.Operations.Dependent
import CORALean.ContSet.PolyZonotope.Float.Operations.MixedForm

/-!
# `PolyZonotope.quadMapMixed`, over a floating-point scalar

CORA's `@polyZonotope/quadMap` at two operands, the float counterpart of
`Real.PolyZonotope.quadMapMixed`: `{(x₁ᵀQ₁x₂, …) | x₁ ∈ pZ₁, x₂ ∈ pZ₂}`, the two arguments ranging
*independently*. As there, `dependent` runs on each operand first, `cartProd` makes their factors
disjoint, and `bilin` pairs the product with itself over those factors, at the form reading the
*first* block of one argument against the *second* block of the other (`mixedForm`). The product
has dimension `n + n`, where the exact layer's lives in `Vec ℝ n × Vec ℝ n`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The quadratic map of two sets whose arguments range independently, CORA's
`quadMap(pZ₁, pZ₂, Q)`. -/
def PolyZonotope.quadMapMixed (Q : Fin m → Mat 𝕋 n n) (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n)) :
    PolyZonotope (Vec 𝕋 m) :=
  let cp := pZ₁.dependent.cartProd pZ₂.dependent
  PolyZonotope.bilin (PolyZonotope.mixedForm Q) cp cp rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
