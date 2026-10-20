module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Plus
public import CORALean.Global.Cost

@[expose] public section

/-!
# `PolyZonotope.plusCost`

Asserted, not proved: `Operations/Plus.lean` adds the two centers, `n` additions at `Vec ℝ n`, and
concatenates the generator blocks and lays the exponent matrices out block-diagonally. That
computes nothing, but every entry of the result is a write: the center and both generator blocks,
and the `p₁ + p₂` by `h₁ + h₂` exponent matrix, zeros included. So the operands' sizes enter.

## Inputs
* `n` – dimension
* `p₁` – first factor count
* `p₂` – second factor count
* `h₁` – first dependent generator count
* `h₂` – second dependent generator count
* `q₁` – first independent generator count
* `q₂` – second independent generator count

## Output
* operation count of the Minkowski sum
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.plus` costs at `Vec ℝ n`, `pᵢ` factors, `hᵢ` dependent and `qᵢ`
independent generators: `n` additions for the center and
`n * (1 + h₁ + h₂ + q₁ + q₂) + (p₁ + p₂) * (h₁ + h₂)` writes for the result. -/
def PolyZonotope.plusCost (n p₁ p₂ h₁ h₂ q₁ q₂ : ℕ) : Cost :=
  ⟨n + (n * (1 + h₁ + h₂ + q₁ + q₂) + (p₁ + p₂) * (h₁ + h₂))⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
