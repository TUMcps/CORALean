import CORALean.ContSet.HPolytope.Real.Operations.Mtimes
import CORALean.Global.Cost

/-!
# `HPolytope.mtimesOfCost`

Asserted, and asserted to be zero: `Operations/Mtimes.lean` builds each row from
`SupportBound.image`, which carries `u.val` over unchanged — the direction is
pulled back through `M` before the certificate is ever asked for, so nothing
here recomputes a bound.
-/

-- Authors:       Tobias Ladner
-- Written:       23-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `HPolytope.mtimesOf` costs: nothing. `SupportBound.image` relabels a
certificate's value rather than recomputing it. -/
def HPolytope.mtimesOfCost : Cost := 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
