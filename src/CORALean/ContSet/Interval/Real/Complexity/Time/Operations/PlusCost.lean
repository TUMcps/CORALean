module

public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.Global.Cost

@[expose] public section

/-!
# `Interval.plusCost`

Asserted, not proved: `Operations/Plus.lean` adds the two lower bounds and the
two upper bounds entrywise, so at `Vec ℝ n` it is `2 * n` additions and `2 * n` writes. No rounding
enters here — that is the float layer's cost, not this one's.

## Inputs
* `n` – dimension

## Output
* time cost of the Minkowski sum in dimension `n`
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Interval.plus` costs at `Vec ℝ n`: one addition per entry of `inf` and one per entry of
`sup`, and as many writes. -/
def Interval.plusCost (n : ℕ) : Cost := ⟨4 * n⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
