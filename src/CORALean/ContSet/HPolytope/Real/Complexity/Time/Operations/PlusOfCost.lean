module

public import CORALean.ContSet.HPolytope.Real.Operations.Plus
public import CORALean.Global.Cost

@[expose] public section

/-!
# `HPolytope.plusOfCost`

Asserted, not proved: `Operations/Plus.lean` builds `q` rows, each one
`SupportBound.add` on the two certificates the caller already holds — one
addition of their `.val`s and nothing else, the certificates themselves being
data this operation only reads.

The result is `q` rows, each a functional of `d` coefficients and a right-hand side, all written.

## Inputs
* `d` – natural number
* `q` – natural number

## Output
* one addition per row and `q * (d + 1)` writes for the result
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       23-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `HPolytope.plusOf` costs at `q` rows over a coefficient space of dimension `d`: one
addition per row, from `SupportBound.add`, and `q * (d + 1)` writes for the result. -/
def HPolytope.plusOfCost (d q : ℕ) : Cost := ⟨q + q * (d + 1)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
