module

public import CORALean.ContSet.ZonoBundle.Real.Operations.Map
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.MapCost

@[expose] public section

/-!
# `ZonoBundle.mapCost`

Asserted, not proved: `Operations/Map.lean` runs `Zonotope.map` once per member
and does nothing of its own, so the count is `k` copies of the zonotope one.

`h` bounds *every* member's generator count, as in `ZonoBundle.mtimesCost`,
since the structure carries a family with no common width.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `ZonoBundle.map` costs at a map costing at most `cf` per application,
on a bundle of `k` members, none of them over `h` generators. -/
def ZonoBundle.mapCost (cf : Cost) (k h : ℕ) : Cost := k • Zonotope.mapCost cf h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
