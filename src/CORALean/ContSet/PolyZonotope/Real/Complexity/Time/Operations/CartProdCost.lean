module

public import CORALean.ContSet.PolyZonotope.Real.Operations.CartProd
public import CORALean.Global.Cost

@[expose] public section

/-!
# `PolyZonotope.cartProdCost`

Asserted, not proved: `Operations/CartProd.lean` pairs the centers, pads each operand's generators
(dependent and independent) with a zero in the other component and assembles the exponent matrix
block-diagonally with `plusE`, whose off-diagonal blocks are literal zeros. Nothing is computed,
but every entry of the result is a write: the center and both generator blocks at `n₁ + n₂`
rows, and the `p₁ + p₂` by `h₁ + h₂` exponent matrix, zeros included.

## Inputs
* `n₁` – first dimension
* `n₂` – second dimension
* `p₁` – first factor count
* `p₂` – second factor count
* `h₁` – first dependent generator count
* `h₂` – second dependent generator count
* `q₁` – first independent generator count
* `q₂` – second independent generator count

## Output
* operation count of the Cartesian product
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.cartProd` costs at `Vec ℝ n₁` and `Vec ℝ n₂` over `pᵢ` factors, `hᵢ`
dependent and `qᵢ` independent generators: one write for each of the
`(n₁ + n₂) * (1 + h₁ + h₂ + q₁ + q₂) + (p₁ + p₂) * (h₁ + h₂)` entries of the result. -/
def PolyZonotope.cartProdCost (n₁ n₂ p₁ p₂ h₁ h₂ q₁ q₂ : ℕ) : Cost :=
  ⟨(n₁ + n₂) * (1 + h₁ + h₂ + q₁ + q₂) + (p₁ + p₂) * (h₁ + h₂)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
