module

public import CORALean.ContSet.Interval.Real.Operations.LinComb
public import CORALean.Global.Cost

@[expose] public section

/-!
# `Interval.linCombCost`

Asserted, not proved: `Operations/LinComb.lean` is the entrywise hull, one
`min` per entry of `inf` and one `max` per entry of `sup`, so at `Vec ℝ n` it
costs the same `2 * n` comparisons and `2 * n` writes as `plus` — no interpolating generator to
build, a box
having no generators to pair.

## Inputs
* `n` – dimension

## Output
* time cost of the linear combination in dimension `n`
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Interval.linComb` costs at `Vec ℝ n`: one `min` per entry of `inf` and one `max` per
entry of `sup`, and as many writes. -/
def Interval.linCombCost (n : ℕ) : Cost := ⟨4 * n⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
