module

public import CORALean.ContSet.Zonotope.Real.Operations.MinkDiffRep
public import CORALean.Global.Cost

@[expose] public section

/-!
# `Zonotope.minkDiffRepCost`

Asserted, not proved: `Operations/MinkDiffRep.lean` at `Vec ℝ n`, a minuend of `h₁` and a
subtrahend of `h₂` generators, `M : h₁ × h₂`. The check that `M` represents `Z₂`'s generators
forms `∑ i, M i j • Z₁.G i` for each `j` (`2 * h₁ * n`) and compares `n` entries; the row-sum check
is `2 * h₂` per row; the result recomputes the row sums and scales the generator
(`h₁ * (2 * h₂ + 1 + n)`), the center is `n` subtractions, and the result writes `n * (h₁ + 1)`
entries. The `none` branch pays for the checks only and writes nothing, which this bounds.

## Inputs
* `n` – dimension
* `h₁` – minuend generator count
* `h₂` – subtrahend generator count

## Output
* cost of the checks, new generators and writes
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.minkDiffRep` costs at `Vec ℝ n`: the checks and the new generators, and
`n * (h₁ + 1)` writes for the result's center and generator matrix. -/
def Zonotope.minkDiffRepCost (n h₁ h₂ : ℕ) : Cost :=
  ⟨h₂ * (2 * h₁ * n + n) + 2 * h₁ * h₂ + h₁ * (2 * h₂ + 1 + n) + n + n * (h₁ + 1)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
