import CORALean.ContSet.HPolytope.Real.Operations.Plus
import CORALean.Global.Cost

/-!
# `HPolytope.plusOfCost`

Asserted, not proved: `Operations/Plus.lean` builds `q` rows, each one
`SupportBound.add` on the two certificates the caller already holds — one
addition of their `.val`s and nothing else, the certificates themselves being
data this operation only reads.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `HPolytope.plusOf` costs at `q` rows: one addition per row, from
`SupportBound.add`. -/
def HPolytope.plusOfCost (q : ℕ) : Cost := ⟨q⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
