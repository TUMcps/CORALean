module

public import CORALean.ContSet.HPolytope.Real.Operations.Mtimes
public import CORALean.Global.Cost

@[expose] public section

/-!
# `HPolytope.mtimesOfCost`

Asserted, and asserted to be zero: `Operations/Mtimes.lean` builds each row from
`SupportBound.image`, which carries `u.val` over unchanged — the direction is
pulled back through `M` before the certificate is ever asked for, so nothing
here recomputes a bound.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `HPolytope.mtimesOf` costs: nothing. `SupportBound.image` relabels a
certificate's value rather than recomputing it. -/
def HPolytope.mtimesOfCost : Cost := 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
