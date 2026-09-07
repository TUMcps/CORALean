import CORALean.ContSet.Zonotope.Real.Operations.LinComb
import CORALean.Global.Cost

/-!
# `Zonotope.linCombCost`

Asserted, not proved, by reading `Operations/LinComb.lean`: the centre
`(1/2) • (c₁ + c₂)` is `n` additions and `n` scalings, the fresh generator
`(1/2) • (c₁ - c₂)` the same again, and each `pairSum` or `pairDiff` column is
`n` additions and `n` scalings where the blocks pair and free where the longer
one runs on alone — bounded above by pairing every column of both.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.linComb` costs at `Vec ℝ n` and `h₁`, `h₂` generators:
`4 * n` for the centre and the fresh generator, `2 * n` per paired column. -/
def Zonotope.linCombCost (n h₁ h₂ : ℕ) : Cost := ⟨4 * n + 2 * n * (h₁ + h₂)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
