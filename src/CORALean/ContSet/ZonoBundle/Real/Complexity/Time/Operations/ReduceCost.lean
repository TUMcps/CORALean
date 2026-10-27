module

public import CORALean.ContSet.ZonoBundle.Real.Operations.Reduce
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.ReduceGirardCost
public import CORALean.Global.Cost

@[expose] public section

/-!
# `ZonoBundle.reduceCost`

Asserted, not proved. CORA's `@zonoBundle/reduce.m` reduces every member by the method asked for,
and `ZonoBundle.reduce` does the same at Girard's rule: `k` members, each at
`Zonotope.reduceGirardCost`, the Girard metric and the selection of each member's generators
included.

An upper bound, not an exact count, because that member cost is one: it charges the metrics and the
sort at their worst and the block `reduceBy` writes at `h` kept and `h` absorbed generators,
whatever the order. The bundle adds nothing of its own, no member is dropped or reordered.

## Inputs
* `n` – dimension
* `k` – number of members
* `h` – generators per member

## Output
* the cost of reducing the bundle
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   27-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `ZonoBundle.reduce` costs at any order at `Vec ℝ n` on a bundle of `k` members, none over
`h` generators: each member reduced, at `Zonotope.reduceGirardCost`. -/
def ZonoBundle.reduceCost (n k h : ℕ) : Cost :=
  k • Zonotope.reduceGirardCost n h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
