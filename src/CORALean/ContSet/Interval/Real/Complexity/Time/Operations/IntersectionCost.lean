module

public import CORALean.ContSet.Interval.Real.Operations.Intersection
public import CORALean.Global.Cost

@[expose] public section

/-!
# `Interval.intersectionCost`

Asserted, not proved: `Operations/Intersection.lean` takes a `max` of the two
lower bounds and a `min` of the two upper bounds entrywise, one comparison
each, so at `Vec ℝ n` it is `2 * n` comparisons, and as many writes.

## Inputs
* `n` – dimension

## Output
* time cost of the intersection in dimension `n`
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       23-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Interval.intersection` costs at `Vec ℝ n`: one comparison per entry of `inf` and one per
entry of `sup`, and as many writes. -/
def Interval.intersectionCost (n : ℕ) : Cost := ⟨4 * n⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
