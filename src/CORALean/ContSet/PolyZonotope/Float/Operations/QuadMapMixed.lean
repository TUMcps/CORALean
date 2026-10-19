module

public import CORALean.ContSet.PolyZonotope.Float.Operations.AbsorbRounding
public import CORALean.ContSet.PolyZonotope.Float.Operations.Bilin
public import CORALean.ContSet.PolyZonotope.Float.Operations.CartProd
public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

@[expose] public section

/-!
# `PolyZonotope.quadMapMixed`, over a floating-point scalar

CORA's `@polyZonotope/quadMap` at two operands, the float counterpart of
`Real.PolyZonotope.quadMapMixed`: `{(x₁ᵀQ₁x₂, …) | x₁ ∈ pZ₁, x₂ ∈ pZ₂}`, the two arguments ranging
*independently*. As there, `absorbRounding` runs on each operand first, `cartProd` makes their
factors disjoint, and `bilin` pairs the product with itself over those factors, at the form reading
the
*first* block of one argument against the *second* block of the other (`aux_mixedForm`). The product
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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `Qₖ` placed to read the first block of a pair against the second: `(x₁, x₂) ↦ (y₁, y₂) ↦
x₁ᵀ Qₖ y₂`. -/
def PolyZonotope.aux_mixedForm (Q : Fin m → Mat 𝕋 n n) : Fin m → Mat 𝕋 (n + n) (n + n) :=
  fun k r r' =>
    Fin.addCases (motive := fun _ => 𝕋)
      (fun a => Fin.addCases (motive := fun _ => 𝕋) (fun _ => zero) (fun b => Q k a b) r')
      (fun _ => zero) r


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The quadratic map of two sets whose arguments range independently, CORA's
`quadMap(pZ₁, pZ₂, Q)`. -/
def PolyZonotope.quadMapMixed (Q : Fin m → Mat 𝕋 n n) (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n)) :
    PolyZonotope (Vec 𝕋 m) :=
  let cp := pZ₁.absorbRounding.cartProd pZ₂.absorbRounding
  PolyZonotope.bilin (PolyZonotope.aux_mixedForm Q) cp cp rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
