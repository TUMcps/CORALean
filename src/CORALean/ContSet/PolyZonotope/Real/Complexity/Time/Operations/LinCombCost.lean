module

public import CORALean.ContSet.PolyZonotope.Real.Operations.LinComb
public import CORALean.Global.Cost

@[expose] public section

/-!
# `PolyZonotope.linCombCost`

Asserted, not proved, by reading `Operations/LinComb.lean`. The center `½(c₁+c₂)` is `n`
additions and `n` scalings, and the fresh dependent generator `½(c₁-c₂)` the same again. Each
of the two dependent blocks scales every column of both operands, `n` scalings a column. The
independent block is `Zonotope.pairSum` and `pairDiff`: `n` additions and scalings per paired
column, bounded by pairing every column of both. Every scalar of the result is also a write.

## Inputs
* `n` – dimension
* `p₁` – first factor count
* `p₂` – second factor count
* `h₁` – first dependent generator count
* `h₂` – second dependent generator count
* `q₁` – first independent generator count
* `q₂` – second independent generator count

## Output
* operation count of the linear combination
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.linComb` costs at `Vec ℝ n`, `pᵢ` factors, `hᵢ`, `qᵢ` generators: `4 * n`
for the center and fresh generator, `2 * n` per dependent or paired column, and the writes of
`n * (2 * (h₁ + h₂) + 2 + q₁ + q₂) + (p₁ + p₂ + 1) * (2 * (h₁ + h₂) + 1)` entries. -/
def PolyZonotope.linCombCost (n p₁ p₂ h₁ h₂ q₁ q₂ : ℕ) : Cost :=
  ⟨4 * n + 2 * n * (h₁ + h₂) + 2 * n * (q₁ + q₂) +
    (n * (2 * (h₁ + h₂) + 2 + q₁ + q₂) + (p₁ + p₂ + 1) * (2 * (h₁ + h₂) + 1))⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
