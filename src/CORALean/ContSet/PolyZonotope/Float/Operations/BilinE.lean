module

public import CORALean.ContSet.PolyZonotope.Float.Operations.ExtE

@[expose] public section

/-!
# `bilin`'s exponent matrix, over a floating-point scalar

The pairing of two sets over the *same* factors: the product of two monomials is the monomial at
the added exponent column, `pZ₂`'s read at `pZ₁`'s factor indices by `hp`. Over ℕ, so exact; the
float counterpart of `Real.PolyZonotope.bilinE`, of which `quadMapE` is the self-pairing.

## Inputs
* `pZ₁` – first polynomial zonotope
* `pZ₂` – second polynomial zonotope

## Hypotheses
* `hp` – both have the same factor count

## Output
* exponent matrix of the bilinear image
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   12-October-2026
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {α β : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Its exponent column, the two columns added. -/
def PolyZonotope.bilinE (pZ₁ : PolyZonotope α) (pZ₂ : PolyZonotope β) (hp : pZ₁.p = pZ₂.p) :
    Fin pZ₁.p → Fin ((pZ₁.h + 1) * (pZ₂.h + 1)) → ℕ :=
  fun k l => PolyZonotope.extE pZ₁ k (finProdFinEquiv.symm l).1
      + PolyZonotope.extE pZ₂ (Fin.cast hp k) (finProdFinEquiv.symm l).2

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
