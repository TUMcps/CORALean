module

public import CORALean.ContSet.HPolytope.Real.Operations.Mtimes
public import CORALean.Global.Cost

@[expose] public section

/-!
# `HPolytope.mtimesOfCost`

Asserted, not proved, and no longer zero: `Operations/Mtimes.lean` builds each row from
`SupportBound.image`, which carries `u.val` over unchanged — the direction is pulled back through
`M` before the certificate is ever asked for, so nothing here recomputes a bound. The result is
`q` inequality rows, each a functional of `d` coefficients and a right-hand side, and writing them
is the cost.

## Inputs
* `d` – natural number
* `q` – natural number

## Output
* one write for each of the `q * (d + 1)` entries of the result
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       23-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `HPolytope.mtimesOf` costs for `q` rows over a coefficient space of dimension `d`: one
write for each of the `q * (d + 1)` entries of the result. -/
def HPolytope.mtimesOfCost (d q : ℕ) : Cost := ⟨q * (d + 1)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
