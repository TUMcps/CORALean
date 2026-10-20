module

public import CORALean.ContSet.ZonoBundle.Real.Operations.Reduce
public import CORALean.Global.Cost

@[expose] public section

/-!
# `ZonoBundle.reduceCost`

Asserted, not proved. CORA's `@zonoBundle/reduce.m` reduces each member by the method asked for, and
a method *selects* the generators it keeps before it writes them: Girard's metric on each generator
(at most `4 * n + 2` operations, as `Zonotope.reduceGirardCost` counts it) and the sort of the `h`
keys, `Cost.sort h`. That selection is charged per member, `k` times, and the kept members are then
written, `n * (h + 1)` entries each.

`Operations/Reduce.lean` itself keeps the first `min k o` members and never looks inside one, so the
count is an upper bound for it, stated at CORA's method; reducing members is `Zonotope.reduce`.

## Inputs
* `n` – dimension
* `k` – number of members
* `h` – generators per member

## Output
* the cost of the order reduction
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `ZonoBundle.reduce` costs at any order at `Vec ℝ n` on a bundle of `k` members, none over
`h` generators: per member, the selection of the generators to keep (Girard's metrics and the
sort of the keys), then one write for each of the at most `k * (n * (h + 1))` entries kept. -/
def ZonoBundle.reduceCost (n k h : ℕ) : Cost :=
  k • (⟨h * (4 * n + 2)⟩ + Cost.sort h) + ⟨k * (n * (h + 1))⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
