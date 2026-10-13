import CORALean.ContSet.ZonoBundle.Real.Operations.Intersection
import CORALean.Global.Cost

/-!
# `ZonoBundle.intersectionCost`

Asserted, not proved, and asserted to be zero: `Operations/Intersection.lean`
concatenates the two families of members and computes nothing at all.

This is what the representation is for. An intersection a zonotope cannot
represent costs a bundle nothing to *take* — the members are kept side by side
and the set they denote is their intersection by definition. What it costs is
paid later and elsewhere, in the `k₁ + k₂` members every subsequent operation
then runs over, which is exactly what `plusCost` and `mtimesCost` charge for.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `ZonoBundle.intersection` costs: nothing. The two families are concatenated and
neither is touched. -/
def ZonoBundle.intersectionCost : Cost := 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
