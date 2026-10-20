module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Plus
public import CORALean.Global.Cost
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.PlusCost

@[expose] public section

/-!
# `ConPolyZono.plusCost`

Asserted, not proved: `Operations/Plus.lean` adds the centers, `n` additions at `Vec ℝ n`, and
lays the generator blocks, the exponent matrices and the constraint blocks out
block-diagonally. That computes nothing, but every entry of the result is a write: those of
`PolyZonotope.plusCost`, and the `(m₁ + m₂)` by `(q₁ + q₂)` matrix `A`, the vector `b` of
`m₁ + m₂` rows and the `(p₁ + p₂)` by `(q₁ + q₂)` matrix `R`, zeros included.

## Inputs
* `n` – ambient dimension
* `p₁` – factors of first summand
* `p₂` – factors of second summand
* `h₁` – dependent generators of first
* `h₂` – dependent generators of second
* `qI₁` – independent generators of first
* `qI₂` – independent generators of second
* `m₁` – constraints of first
* `m₂` – constraints of second
* `q₁` – constraint generators of first
* `q₂` – constraint generators of second

## Output
* cost of the Minkowski sum
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       23-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `ConPolyZono.plus` costs at `Vec ℝ n`, `pᵢ` factors, `hᵢ`, `qIᵢ` generators, `mᵢ`
constraints over `qᵢ`: the polynomial zonotope's sum and the writes of the constraint block,
`(m₁ + m₂) * (q₁ + q₂) + (m₁ + m₂) + (p₁ + p₂) * (q₁ + q₂)`. -/
def ConPolyZono.plusCost (n p₁ p₂ h₁ h₂ qI₁ qI₂ m₁ m₂ q₁ q₂ : ℕ) : Cost :=
  PolyZonotope.plusCost n p₁ p₂ h₁ h₂ qI₁ qI₂ +
    ⟨(m₁ + m₂) * (q₁ + q₂) + (m₁ + m₂) + (p₁ + p₂) * (q₁ + q₂)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
