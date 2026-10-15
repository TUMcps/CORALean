module

public import CORALean.ContSet.ZonoBundle.Real.Operations.Reduce
public import CORALean.Global.Cost

@[expose] public section

/-!
# `ZonoBundle.reduceCost`

Asserted, not proved: `Operations/Reduce.lean` keeps the first `min k o` members and drops the
rest, and never looks inside one. No arithmetic, but the members that stay are written into the
result, `n * (h + 1)` entries each.

Worth stating precisely because the name misleads. Every other `reduce` in the
tree spends work to shrink a generator count; this one bounds the *member*
count, by truncation, and leaves each member at whatever order it already had.
A caller who wants the members reduced runs `Zonotope.reduce` on them, and pays
`Zonotope.reduceGirardCost` per member for it.
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `ZonoBundle.reduce` costs at any order at `Vec ℝ n` on a bundle of `k` members, none over
`h` generators: one write for each of the at most `k * (n * (h + 1))` entries kept. -/
def ZonoBundle.reduceCost (n k h : ℕ) : Cost := ⟨k * (n * (h + 1))⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
