module

public import CORALean.ContSet.Zonotope.Real.Operations.LinComb
public import CORALean.Global.Cost

@[expose] public section

/-!
# `Zonotope.linCombCost`

Asserted, not proved, by reading `Operations/LinComb.lean`: the center
`(1/2) • (c₁ + c₂)` is `n` additions and `n` scalings, the fresh generator
`(1/2) • (c₁ - c₂)` the same again, and each `pairSum` or `pairDiff` column is
`n` additions and `n` scalings where the blocks pair and free where the longer
one runs on alone — bounded above by pairing every column of both.

Under `Global/Cost.lean`'s model every scalar of the result is also a write, one unit each, and the
result has `n * (h₁ + h₂ + 2)` of them: the center and the `h₁ + h₂ + 1`
generators.
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.linComb` costs at `Vec ℝ n` and `h₁`, `h₂` generators: `4 * n` for the center
and the fresh generator, `2 * n` per paired column, and `n * (h₁ + h₂ + 2)` writes, one for each
entry of the result. -/
def Zonotope.linCombCost (n h₁ h₂ : ℕ) : Cost :=
  ⟨4 * n + 2 * n * (h₁ + h₂) + n * (h₁ + h₂ + 2)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
