import CORALean.ContSet.PolyZonotope.Real.Operations.LinComb
import CORALean.Global.Cost

/-!
# `PolyZonotope.linCombCost`

Asserted, not proved, by reading `Operations/LinComb.lean`. The centre
`½(c₁+c₂)` is `n` additions and `n` scalings, and the one fresh dependent
generator `½(c₁-c₂)` the same again. Each of the two dependent blocks scales
every column of both operands, `n` scalings a column, and the second negates
`pZ₂`'s as it scales — folded into the same `n`, a sign being part of the
constant.

The independent block is `Zonotope.pairSum` and `pairDiff`: `n` additions and
`n` scalings per paired column, free where the longer block runs on alone,
bounded above by pairing every column of both. `linCombE` writes zeros and ones
and computes nothing.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.linComb` costs at `Vec ℝ n`: `4 * n` for the centre and
the fresh generator, `2 * n` per dependent column, `2 * n` per paired one. -/
def PolyZonotope.linCombCost (n h₁ h₂ q₁ q₂ : ℕ) : Cost :=
  ⟨4 * n + 2 * n * (h₁ + h₂) + 2 * n * (q₁ + q₂)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
