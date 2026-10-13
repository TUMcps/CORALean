import CORALean.ContSet.ZonoBundle.Real.Operations.Reduce
import CORALean.Global.Cost

/-!
# `ZonoBundle.reduceCost`

Asserted, not proved, and asserted to be zero: `Operations/Reduce.lean` keeps
the first `min k o` members and drops the rest, and never looks inside one.

Worth stating precisely because the name misleads. Every other `reduce` in the
tree spends work to shrink a generator count; this one bounds the *member*
count, by truncation, and leaves each member at whatever order it already had.
A caller who wants the members reduced runs `Zonotope.reduce` on them, and pays
`Zonotope.reduceGirardCost` per member for it.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `ZonoBundle.reduce` costs at any order: nothing. Truncating the family
is index work, and no member is touched. -/
def ZonoBundle.reduceCost : Cost := 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
