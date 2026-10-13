import CORALean.ContSet.Zonotope.Real.Operations.MinkDiffRep
import CORALean.Global.Cost

/-!
# `Zonotope.minkDiffRepCost`

Asserted, not proved: `Operations/MinkDiffRep.lean` at `Vec ℝ n`, a minuend of
`h₁` and a subtrahend of `h₂` generators, `M : h₁ × h₂`. The check that `M`
represents `Z₂`'s generators forms `∑ i, M i j • Z₁.G i` for each `j`
(`2 * h₁ * n`) and compares `n` entries; the row-sum check is `2 * h₂` per row;
the result recomputes the row sums, subtracts them from one and scales the
generator (`h₁ * (2 * h₂ + 1 + n)`), and the centre is `n` subtractions. The
`none` branch pays for the checks only, which this bounds.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.minkDiffRep` costs at `Vec ℝ n`. -/
def Zonotope.minkDiffRepCost (n h₁ h₂ : ℕ) : Cost :=
  ⟨h₂ * (2 * h₁ * n + n) + 2 * h₁ * h₂ + h₁ * (2 * h₂ + 1 + n) + n⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
